{-# LANGUAGE ImplicitParams #-}

-- Interface to SMT2 format

module Solver.SMTLib2(SMT2Config,
               z3Config,
               newSMTLib2Solver) where

import Prelude hiding ((<>))

import qualified Text.Parsec as P
import Text.PrettyPrint
import System.IO.Unsafe
import System.Process
import System.Exit
import Control.Monad.Except
import Control.Applicative hiding (empty)
import Data.List
import Data.Maybe
import Data.String.Utils
import qualified Data.Set             as S
import qualified Data.Map             as M
import Debug.Trace

import TSLUtil
import Util hiding (trace)
import Ops
import Abstract.Predicate
import Abstract.BFormula
import Abstract.AbsRelation
import Internal.ISpec
import Internal.IVar
import Internal.IType
import Internal.IExpr
import Solver.SMTLib2Parse
import Solver.Store
import Solver.SMTSolver
import Abstract.MkPredicate

data SMT2Config = SMT2Config {
    s2Solver :: String,  -- Name of the solver executable
    s2Opts   :: [String] -- Arguments passed on every invocation of the solver
}

z3Config = SMT2Config {s2Solver = "z3", s2Opts = ["-smt2", "-in"]}

newSMTLib2Solver :: Spec -> SMT2Config -> SMTSolver
newSMTLib2Solver spec config = SMTSolver { smtGetModel       = let ?spec = spec in getModel config
                                         , smtCheckSAT       = let ?spec = spec in checkSat config
                                         , smtGetCore        = let ?spec = spec in getUnsatCore config
                                         , smtGetModelOrCore = let ?spec = spec in getModelOrCore config
                                         }

------------------------------------------------------
-- Printing formulas in SMTLib2 format
------------------------------------------------------

class SMTPP a where
    smtpp :: (?spec::Spec, ?typemap::M.Map Type String) => a -> Doc

mkFormulas :: (?spec::Spec) => [Formula] -> (Doc, [(String, Term)])
mkFormulas fs = 
    let fs' = map expandRels fs
        vars = S.toList $ S.fromList $ concatMap fVar fs'
        rpreds = nub $ concatMap fRelations fs'
        (typemap, typedecls) = mkTypeMap vars in
    let ?typemap = typemap in
    let (ptrvars, ptrconstr, ptrmap) = mkPtrConstraints fs' in
        (-- type declarations
         typedecls 
         $+$
         -- variable declarations
         (vcat $ map smtpp vars)
         $+$
         (vcat $ map declRel rpreds)
         $+$
         ptrvars
         $+$
         -- formulas
         (vcat $ mapIdx (\f i -> parens $ text "assert" 
                                          <+> (parens $ char '!' <+> smtpp f <+> text ":named" <+> text assertName <> int i)) fs')
         $+$
         -- pointer consistency constraints
         ptrconstr
         ,
         ptrmap)

-- For each relation predicate in the formula, expand all rules for this relation
-- and add them to the formula, so that the predicate can be replaced with a boolean
-- variable without losing precision
expandRels :: (?spec::Spec) => Formula -> Formula
expandRels f = fbinop Conj f $
               (fconj $ map (\(p, rules) -> fconj $ map (\(op,r) -> case op of
                                                                         Implies -> fbinop Impl (FBoolAVar $ AVarPred p) (ptrFreeBExprToFormula r)
                                                                         Implied -> fbinop Impl (ptrFreeBExprToFormula r) (FBoolAVar $ AVarPred p)
                                                                         Iff     -> fbinop Equiv (FBoolAVar $ AVarPred p) (ptrFreeBExprToFormula r)) 
                                                    rules)
                      $ map (\(n, args) -> instantiateRelation (getRelation n) args)
                      $ fRelations f)

fRelations :: (?spec::Spec) => Formula -> [(String, [Expr])]
fRelations f = mapMaybe (\av -> case av of
                                     AVarPred (PRel n args) -> Just (n, args)
                                     _                      -> Nothing)
               $ fAbsVars f 

declRel :: (?spec::Spec, ?typemap::M.Map Type String) => (String, [Expr]) -> Doc
declRel (n, args) = parens $ text "declare-const" <+> vname <+> text "Bool"
    where vname = smtpp (PRel n args)

instance SMTPP Var where
    smtpp v = parens $  text "declare-const"
                    <+> text (mkIdent $ varName v)
                    <+> text (?typemap M.! (varType v))

-- convert string into a valid smtlib identifier by
-- bracketing it with '|' if necessary
mkIdent :: String -> String
mkIdent str = if valid then str else "|" ++ (replace  "|" "_" str) ++ "|"
    where valid = all (\c -> elem c ("_"++['a'..'z']++['A'..'Z']++['0'..'9'])) str
                  && notElem (head str) ['0'..'9']

mkTypeMap :: (?spec::Spec) => [Var] -> (M.Map Type String, Doc)
mkTypeMap vs = foldl' mkTypeMap' (M.empty, empty) alltypes
    where -- sort all types occurring in the spec in dependency order
          alltypes = sortBy (\t1 t2 -> if' (elem t1 $ subtypesRec t2) LT $
                                       if' (elem t2 $ subtypesRec t1) GT $
                                       EQ)
                     $ nub $ concatMap (subtypesRec . typ) vs

mkTypeMap' :: (?spec::Spec) => (M.Map Type String, Doc) -> Type -> (M.Map Type String, Doc)
mkTypeMap' (m,doc) t = let (tname, tdecl) = mkTypeMap1 m t
                       in (M.insert t tname m, doc $$ tdecl)

subtypes :: Type -> [Type]
subtypes (Bool _)      = []
subtypes (SInt _ _)    = []
subtypes (UInt _ _)    = []
subtypes (Enum _ _)    = []
subtypes (Struct _ fs) = map typ fs
subtypes (Array _ t _) = [t]
subtypes (Ptr _ t)     = [t]

subtypesRec :: Type -> [Type]
subtypesRec t = t:(concatMap subtypesRec $ subtypes t)

mkTypeMap1 :: (?spec::Spec) => M.Map Type String -> Type -> (String, Doc)
mkTypeMap1 _ (Bool _)      = ( "Bool"                                  
                             , empty)
mkTypeMap1 _ (SInt _ w)    = ( "(_ BitVec " ++ show w ++ ")"
                             , empty)
mkTypeMap1 _ (UInt _ w)    = ( "(_ BitVec " ++ show w ++ ")"
                             , empty)
mkTypeMap1 _ (Enum _ n)    = ( mkIdent n
                             , parens $ text "declare-datatypes ()" <+> (parens $ parens $ hsep $ map (text . mkIdent)
                                                                         -- filter out parens to work around errors in parser
                                                                         $ (filter (\c -> notElem c "()") n):(enumEnums $ getEnumeration n)))
mkTypeMap1 m (Struct _ fs) = ( mkIdent tname
                             , parens $ text "declare-datatypes ()" 
                                        <+> (parens $ parens $ text tname 
                                             <+> parens (text ("mk-" ++ tname) <+> (hsep $ map (\(Field n t) -> parens $ text (tname ++ n) <+> text (m M.! t)) fs))))
                             where tname = "Struct" ++ (show $ M.size m)
mkTypeMap1 m (Ptr _ t)     = ( tname
                             , parens $ text "declare-sort" <+> text tname)
                             where tname = ptrTypeName m t
mkTypeMap1 m (Array _ t l) = ( "(Array (_ BitVec " ++ (show $ bitWidth $ l - 1) ++ ") " ++ m M.! t ++ ")"
                             , empty)

ptrTypeName :: (Typed a) => M.Map Type String -> a -> String
ptrTypeName m t = mkIdent $ "Ptr" ++ (m M.! typ t)

addrofVarName :: Term -> String
addrofVarName t = mkIdent $ "addrof-" ++ show t

instance SMTPP Formula where
    smtpp FTrue                       = text "true"
    smtpp FFalse                      = text "false"
    smtpp (FBoolAVar (AVarPred p))    = smtpp p
    smtpp (FBoolAVar (AVarBool t))    = smtpp t
    smtpp (FEq v1 v2)                 = parens $ smtpp REq <+> smtpp v1 <+> smtpp v2
    smtpp (FEqConst v@(AVarEnum t) i) = if i >= (length $ enumEnums $ getEnumeration n)
                                           then trace ("WARNING: smtpp: enum value out of bounds: " ++ n ++ "=" ++ show i) $ text "false"
                                           else parens $ smtpp REq <+> smtpp v <+> 
                                                (text $ mkIdent $ (enumEnums $ getEnumeration n) !! i)
                                        where Enum _ n = termType t
    smtpp (FEqConst v@(AVarInt _) i)  = parens $ smtpp REq <+> smtpp v <+> (text $ "(_ bv" ++ show i ++ " " ++ (show $ avarWidth v) ++ ")")
    smtpp (FBinOp op f1 f2)           = parens $ smtpp op <+> smtpp f1 <+> smtpp f2
    smtpp (FNot f)                    = parens $ text "not" <+> smtpp f

instance SMTPP Predicate where
    smtpp (PAtom op pt1 pt2) | (isInt $ termType t1) = parens $ smtpp op <+> (smtpp $ termPad w t1) <+> (smtpp $ termPad w t2)
                                                       where t1 = ptermTerm pt1
                                                             t2 = ptermTerm pt2
                                                             w = max (termWidth t1) (termWidth t2)
    smtpp (PAtom op pt1 pt2)                         = parens $ smtpp op <+> smtpp pt1 <+> smtpp pt2
    smtpp (PRel n args)                              = text $ mkIdent $ n ++ "(" ++ (intercalate "," $ map show args) ++ ")"

instance SMTPP Term where
    smtpp (TVar n)               = text $ mkIdent n
    smtpp (TSInt w v) |v>=0      = text $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
                      |otherwise = text $ "(bvneg (_ bv" ++ show (-v) ++ " " ++ show w ++ "))"
    smtpp (TUInt w v)            = text $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
    smtpp (TEnum n)              = text $ mkIdent n
    smtpp TTrue                  = text "true"
    smtpp (TAddr t)              = text $ addrofVarName t
    smtpp (TField t f)           = parens $ text ((?typemap M.! termType t) ++ f) <+> smtpp t
    smtpp (TIndex a i)           = parens $ text "select" <+> smtpp a <+> smtpp i
    smtpp (TUnOp op t)           = parens $ smtpp op <+> smtpp t
    -- z3's handling of module division is dodgy, so try to get away with bit slicing instead
    smtpp (TBinOp AMod t1 t2)    | isConstTerm t2 && (isPow2 $ ivalVal $ evalConstTerm t2) 
                                 = smtpp (TSlice t1 (0, (log2 $ ivalVal $ evalConstTerm t2) - 1))
    smtpp (TBinOp op t1 t2)      | (isInt $ termType t1) && (elem op [ABAnd, ABOr, ABXor, APlus, ABinMinus, AMod, AMul]) -- bit vector ops only work on arguments of the same width
                                 = parens $ smtpp op <+> smtpp t1' <+> smtpp t2'
                                   where w = max (termWidth t1) (termWidth t2)
                                         t1' = termPad w t1
                                         t2' = termPad w t2
    smtpp (TBinOp op t1 t2)      = parens $ smtpp op <+> smtpp t1 <+> smtpp t2
    smtpp (TSlice t (l,h))       = parens $ (parens $ char '_' <+> text "extract" <+> int h <+> int l) <+> smtpp t

instance SMTPP PTerm where
    smtpp = smtpp . ptermTerm

instance SMTPP AbsVar where
    smtpp (AVarPred p) = smtpp p
    smtpp (AVarBool t) = smtpp t
    smtpp (AVarInt  t) = smtpp t
    smtpp (AVarEnum t) = smtpp t

instance SMTPP RelOp where
    smtpp REq  = text "="
    smtpp RNeq = text "distinct"
    smtpp RLt  = text "bvult"
    smtpp RGt  = text "bvugt"
    smtpp RLte = text "bvule"
    smtpp RGte = text "bvuge"

instance SMTPP PredOp where
    smtpp PEq  = smtpp REq
    smtpp PLt  = smtpp RLt
    smtpp PLte = smtpp RLte

instance SMTPP ArithUOp where
    smtpp AUMinus = text "bvneg"
    smtpp ABNeg   = text "bvnot"

instance SMTPP ArithBOp where
    smtpp ABAnd     = text "bvand"
    smtpp ABOr      = text "bvor"
    smtpp ABXor     = text "bvxor"
    smtpp ABConcat  = text "concat"
    smtpp APlus     = text "bvadd"
    smtpp ABinMinus = text "bvsub"
    smtpp AMod      = text "bvurem"
    smtpp AMul      = text "bvmul"

instance SMTPP BoolBOp where
    smtpp Conj      = text "and"
    smtpp Disj      = text "or"
    smtpp Impl      = text "=>"
    smtpp Equiv     = text "="

------------------------------------------------------
-- Pointer-related stuff
------------------------------------------------------

-- Consider all pairs of address-of terms of matching 
-- types that occur in the formulas and generate
-- conditions on when these terms are equal, namely:
-- * &x != &y if x and y are distinct variables
-- * &x[i] == &x[j] iff i==j
-- Returns:
-- * a bunch of constant declarations, one for 
--   each address-of term that occurs in the formulas 
-- * the generated condition over these variables
-- * a map from constant names to the terms they represent
mkPtrConstraints :: (?spec::Spec, ?typemap::M.Map Type String) => [Formula] -> (Doc, Doc, [(String, Term)])
mkPtrConstraints fs =
    if' (null addrterms) (empty, empty, [])
    $ (vcat $ map mkAddrofVar addrterms,
       parens 
       $ ((text "and") <+> )
       $ hsep 
       $ concatMap (map (smtpp . ptrEqConstr) . pairs)
       $ sortAndGroup termType addrterms,
       map (\t -> (addrofVarName t, t)) addrterms)
    where addrterms = nub $ concatMap faddrofTerms fs
          

mkAddrofVar :: (?spec::Spec, ?typemap::M.Map Type String) => Term -> Doc
mkAddrofVar t = parens $ text "declare-const" 
                     <+> text (addrofVarName t)
                     <+> text (ptrTypeName ?typemap $ termType t)

faddrofTerms :: (?spec::Spec, ?typemap::M.Map Type String) => Formula -> [Term]
faddrofTerms = nub . faddrofTerms'

faddrofTerms' :: (?spec::Spec, ?typemap::M.Map Type String) => Formula -> [Term]
faddrofTerms' FTrue            = []
faddrofTerms' FFalse           = []
faddrofTerms' (FBoolAVar av)   = concatMap taddrofTerms $ avarTerms av
faddrofTerms' (FEq av1 av2)    = concatMap taddrofTerms $ avarTerms av1 ++ avarTerms av2
faddrofTerms' (FEqConst av _)  = concatMap taddrofTerms $ avarTerms av
faddrofTerms' (FBinOp _ f1 f2) = faddrofTerms' f1 ++ faddrofTerms' f2
faddrofTerms' (FNot f)         = faddrofTerms' f

taddrofTerms :: Term -> [Term]
taddrofTerms (TAddr t) = [t]
taddrofTerms _         = []

ptrEqConstr :: (?spec::Spec, ?typemap::M.Map Type String) => (Term, Term) -> Formula
ptrEqConstr (t1, t2) = case ptrEqCond t1 t2 of
                            FFalse -> neq (TAddr t1) (TAddr t2)
                            f      -> fbinop Equiv (eq (TAddr t1) (TAddr t2)) f

eq  t1 t2 = fRel REq (termToExpr t1) (termToExpr t2)
neq t1 t2 = fnot $ eq t1 t2

ptrEqCond :: (?spec::Spec, ?typemap::M.Map Type String) => Term -> Term -> Formula
ptrEqCond (TField s1 f1) (TField s2 f2) | f1 == f2 = ptrEqCond s1 s2
ptrEqCond (TIndex a1 i1) (TIndex a2 i2)            = fconj [ptrEqCond a1 a2, eq i1 i2]
ptrEqCond (TSlice v1 s1) (TSlice v2 s2) | s1 == s2 = ptrEqCond v1 v2
ptrEqCond _              _                         = FFalse

------------------------------------------------------
-- Running solver in different modes
------------------------------------------------------

runSolver :: SMT2Config -> Doc -> P.Parsec String () a -> a
runSolver cfg spec parser = 
    let (ecode, out, er) = unsafePerformIO $ readProcessWithExitCode (s2Solver cfg) (s2Opts cfg) (show spec)
    in if' (ecode == ExitSuccess || ecode == ExitFailure 1)
           (case P.parse parser "" out of
                 Left e  -> error $ "Error parsing SMT solver output: " ++ 
                                    "\nsolver input: " ++ render spec ++
                                    "\nsolver stdout: " ++ out ++
                                    "\nsolver stderr: " ++ er ++
                                    "\nparser error: "++ show e
                 Right x -> x
                            {-trace "solver input: " 
                            $ trace (render spec)
                            $ trace " solver output: " 
                            $ trace out x-}) 
           (error $ "Error code returned by SMT solver: " ++ show ecode ++
                    "\nsolver input: " ++ render spec ++
                    "\nsolver stdout: " ++ out ++
                    "\nsolver stderr: " ++ er)

checkSat :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe Bool
checkSat cfg fs = runSolver cfg spec satresParser
    where spec = (fst $ mkFormulas fs)
              $$ text "(check-sat)"


getUnsatCore :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe (Maybe [Int])
getUnsatCore cfg fs =
    runSolver cfg spec
    $ do res <- satresParser
         case res of
              Just False -> liftM (Just . Just) unsatcoreParser
              Just True  -> return (Just Nothing)
              _          -> return Nothing
    where spec = text "(set-option :produce-unsat-cores true)"
              $$ (fst $ mkFormulas fs)
              $$ text "(check-sat)"
              $$ text "(get-unsat-core)"

getModel :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe (Maybe Store)
getModel cfg fs = 
    runSolver cfg spec
    $ do res <- satresParser
         case res of 
              Just True  -> liftM (Just . Just) $ modelParser ptrmap
              Just False -> return $ Just Nothing
              _          -> return Nothing
    where (spec0, ptrmap) = mkFormulas fs
          spec = text "(set-option :produce-models true)"
              $$ spec0
              $$ text "(check-sat)"
              $$ text "(get-model)"

getModelOrCore :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe (Either [Int] Store)
getModelOrCore cfg fs = 
    runSolver cfg spec
    $ do res <- satresParser
         case res of 
              Just True  -> liftM (Just . Right) $ modelParser ptrmap
              Just False -> liftM (Just . Left)  $ errorParser *> unsatcoreParser
              _          -> return Nothing
    where (spec0, ptrmap) = mkFormulas fs
          spec = text "(set-option :produce-unsat-cores true)"
              $$ text "(set-option :produce-models true)"
              $$ spec0
              $$ text "(check-sat)"
              $$ text "(get-model)"
              $$ text "(get-unsat-core)"              
