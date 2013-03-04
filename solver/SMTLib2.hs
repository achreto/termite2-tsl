{-# LANGUAGE ImplicitParams #-}

-- Interface to SMT2 format

module SMTLib2() where

import Text.PrettyPrint
import qualified Text.Parsec          as P
import qualified Text.Parsec.Language as P
import qualified Text.Parsec.Token    as PT
import System.IO.Unsafe
import System.Process
import System.Exit
import Control.Monad.Error
import Control.Applicative hiding (many,optional,Const,empty)
import Data.List
import qualified Data.Set             as S
import qualified Data.Map             as M

import Util
import Predicate
import BFormula
import ISpec
import IVar
import IType

data SMT2Config = SMT2Config {
    s2Solver :: String,  -- Name of the solver executable
    s2Opts   :: [String] -- Arguments passed on every invocation of the solver
}

------------------------------------------------------
-- Printing formulas in SMTLib2 format
------------------------------------------------------

class SMTPP a where
    smtpp :: a -> Doc

instance (?spec::Spec) => SMTPP [Formula] where
    smtpp fs = 
        let (typemap, typedecls) = mkTypeMap vars
            vars = S.toList $ S.fromList $ concatMap fVar fs
        in let ?typemap = typemap
           in -- type declarations
              typedecls 
              $+$
              -- variable declarations
              (vcat $ map smtpp vars)
              $+$
              -- formulas
              (vcat $ mapIdx (\f i -> parens $ text "assert" 
                                               <+> (parens $ char '!' <+> smtpp f <+> text ":named" <+> text "a" <> int i)) fs)
              $+$
              -- pointer consistency constraints
              mkPtrConstraints typemap fs

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Var where
    smtpp v = parens $  text "declare-const"
                    <+> text (mkIdent $ varName v)
                    <+> text (?typemap M.! (varType v))

-- convert string into a valid smtlib identifier by
-- bracketing it with '|' if necessary
mkIdent :: String -> String
mkIdent str = if valid then str else "|" ++ str ++ "|"
    where valid = all (\c -> elem c ("_"++['a'..'z']++['A'..'Z']++['0'..'9'])) str
                  && notElem (head str) ['0'..'9']

mkTypeMap :: (?spec::Spec) => [Var] -> (M.Map Type String, Doc)
mkTypeMap vs = foldl' (\m v -> mkTypeMap' m (varType v)) (M.empty, empty) vs

mkTypeMap' :: (?spec::Spec) => (M.Map Type String, Doc) -> Type -> (M.Map Type String, Doc)
mkTypeMap' (m,doc) t = if M.member t m
                          then (m,doc)
                          else let (m', doc') = foldl' mkTypeMap' (m,doc) (subtypes t)
                                   (tname, tdecl) = mkTypeMap1 m' t
                               in (M.insert t tname m', doc' $$ tdecl)

subtypes :: Type -> [Type]
subtypes Bool        = []
subtypes (SInt _)    = []
subtypes (UInt _)    = []
subtypes (Enum _)    = []
subtypes (Struct fs) = map typ fs
subtypes (Array t _) = [t]
subtypes (Ptr t)     = [t]

mkTypeMap1 :: (?spec::Spec) => M.Map Type String -> Type -> (String, Doc)
mkTypeMap1 _ Bool        = ( "Bool"                                  
                           , empty)
mkTypeMap1 _ (SInt w)    = ( "(_ BitVec " ++ show w ++ ")"
                           , empty)
mkTypeMap1 _ (UInt w)    = ( "(_ BitVec " ++ show w ++ ")"
                           , empty)
mkTypeMap1 _ (Enum n)    = ( n
                           , parens $ text "declare-datatypes ()" <+> (parens $ parens $ hsep $ map text $ n:(enumEnums $ getEnumeration n)))
mkTypeMap1 m (Struct fs) = ( tname
                           , parens $ text "declare-datatypes ()" 
                                      <+> (parens $ parens $ text tname 
                                           <+> (hsep $ map (\(Field n t) -> parens $ text (tname ++ n) <+> text (m M.! t)) fs)))
                           where tname = "Struct" ++ (show $ M.size m)
mkTypeMap1 m (Ptr t)     = ( tname
                           , parens $ text "declare-sort" <+> text tname)
                           where tname = ptrTypeName m t
mkTypeMap1 m (Array t s) = ( "(Array Int " ++ m M.! t ++ ")"
                           , empty)

ptrTypeName :: M.Map Type String -> Type -> String
ptrTypeName m t = mkIdent $ "Ptr" ++ (m M.! t)

addrofFuncName :: M.Map Type String -> Type -> String
addrofFuncName m t = mkIdent $ "addrof" ++ (m M.! t)

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Formula where
    smtpp FTrue             = text "true"
    smtpp FFalse            = text "false"
    smtpp (FPred p)         = smtpp p
    smtpp (FBinOp op f1 f2) = parens $ smtpp op <+> smtpp f1 <+> smtpp f2
    smtpp (FNot f)          = parens $ text "not" <+> smtpp f

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Predicate where
    smtpp (PAtom op t1 t2) = parens $ smtpp op <+> smtpp t1 <+> smtpp t2

instance (?spec::Spec, ?typemap::M.Map Type String) => SMTPP Term where
    smtpp (TVar n)               = text $ mkIdent n
    smtpp (TSInt w v) |v>=0      = text $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
                      |otherwise = text $ "(bvneg (_ bv" ++ show (-v) ++ " " ++ show w ++ "))"
    smtpp (TUInt w v)            = text $ "(_ bv" ++ show v ++ " " ++ show w ++ ")"
    smtpp (TEnum n)              = text n
    smtpp TTrue                  = text "true"
    smtpp (TAddr t)              = parens $ text "addr-of" <+> smtpp t
    smtpp (TField t f)           = parens $ text ((?typemap M.! typ t) ++ f) <+> smtpp t
    smtpp (TIndex a i)           = parens $ text "select" <+> smtpp a <+> smtpp i
    smtpp (TUnOp op t)           = parens $ smtpp op <+> smtpp t
    smtpp (TBinOp op t1 t2)      = parens $ smtpp op <+> smtpp t1 <+> smtpp t2
    smtpp (TSlice t (l,h))       = parens $ (parens $ char '_' <+> text "extract" <+> int l <+> int h) <+> smtpp t

instance SMTPP RelOp where
    smtpp REq  = text "="
    smtpp RLt  = text "bvslt"
    smtpp RGt  = text "bvsgt"
    smtpp RLte = text "bvsle"
    smtpp RGte = text "bvsge"

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
    smtpp AMod      = text "bvsmod"
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

mkPtrConstraints :: (?spec::Spec) => M.Map Type String -> [Formula] -> Doc
mkPtrConstraints m fs =
    let ?typemap = m  
    in parens 
       $ ((text "and") <+> )
       $ hsep 
       $ concatMap (map (smtpp . ptrEqConstr) . pairs)
       $ sortAndGroup (\t1 t2 -> typ t1 == typ t2) 
       $ S.toList $ S.fromList 
       $ concatMap faddrofTerms fs

faddrofTerms :: (?spec::Spec, ?typemap::M.Map Type String) => Formula -> [Term]
faddrofTerms FTrue                   = []
faddrofTerms FFalse                  = []
faddrofTerms (FPred (PAtom _ t1 t2)) = taddrofTerms t1 ++ taddrofTerms t2
faddrofTerms (FBinOp _ f1 f2)        = faddrofTerms f1 ++ faddrofTerms f2
faddrofTerms (FNot f)                = faddrofTerms f

taddrofTerms :: Term -> [Term]
taddrofTerms (TAddr t) = [t]
taddrofTerms _         = []

ptrEqConstr :: (?spec::Spec, ?typemap::M.Map Type String) => (Term, Term) -> Formula
ptrEqConstr (t1, t2) = case ptrEqCond t1 t2 of
                           FFalse -> neq (TAddr t1) (TAddr t2)
                           f      -> FBinOp Equiv (eq (TAddr t1) (TAddr t2)) f

eq  t1 t2 = FPred $ PAtom REq t1 t2
neq t1 t2 = FNot $ eq t1 t2

ptrEqCond :: (?spec::Spec, ?typemap::M.Map Type String) => Term -> Term -> Formula
ptrEqCond t1@(TField s1 f1) t2@(TField s2 f2) | f1 == f2 = ptrEqCond s1 s2
ptrEqCond t1@(TIndex a1 i1) t2@(TIndex a2 i2)            = fconj [ptrEqCond a1 a2, eq i1 i2]
ptrEqCond t1@(TSlice v1 s1) t2@(TSlice v2 s2) | s1 == s2 = ptrEqCond v1 v2
ptrEqCond _                 _                            = FFalse

------------------------------------------------------
-- Parsing solver output
------------------------------------------------------

lexer  = PT.makeTokenParser P.emptyDef

lidentifier = PT.identifier lexer
lsymbol     = PT.symbol     lexer
ldecimal    = PT.decimal    lexer
lparens     = PT.parens     lexer

satres = ((Just False) <$ lsymbol "unsat") <|> 
         ((Just True)  <$ lsymbol "sat")

unsatcore :: P.Parsec String () [Int]
unsatcore = P.option [] (lparens $ P.many $ (P.char 'a' *> (fromInteger <$> ldecimal)))

------------------------------------------------------
-- Running solver in different modes
------------------------------------------------------

runSolver :: SMT2Config -> Doc -> P.Parsec String () a -> a
runSolver cfg spec parser = 
    let (retcode, out, err) = unsafePerformIO $ readProcessWithExitCode (s2Solver cfg) (s2Opts cfg) (show spec)
    in if retcode == ExitSuccess 
          then case P.parse parser "" out of
                    Left e  -> error $ "Error parsing SMT solver output: " ++ show e
                    Right x -> x
          else error $ "Error running SMT solver: " ++ err

checkSat :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe Bool
checkSat cfg fs = runSolver cfg spec satres
    where spec = smtpp fs 
              $$ text "(check-sat)"


getUnsatCore :: (?spec::Spec) => SMT2Config -> [Formula] -> Maybe [Int]
getUnsatCore cfg fs =
    runSolver cfg spec
    $ ((\res core -> case res of
                          Just False -> Just core
                          _          -> Nothing)
       <$> satres <*> unsatcore)
    where spec = text "(set-option :produce-unsat-cores true)"
              $$ smtpp fs 
              $$ text "(check-sat)"
              $$ text "(get-unsat-core)"
