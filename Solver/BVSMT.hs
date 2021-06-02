-- Theory solver that uses bitvector library for existential quantification
-- and SMTLib2 for satisfiability checking and unsat cores

{-# LANGUAGE ImplicitParams, RecordWildCards, ConstraintKinds, FlexibleContexts #-}

module Solver.BVSMT(VarAsn(..),
             bvSolver,
             bvSolve,
             bvRelNormalise,
             bvTermNormalise) where

import Data.Maybe
import Data.List
import Control.Monad.State.Lazy
import Control.Monad.ST
import qualified Data.Map as M
import Debug.Trace

import Util hiding (trace)
import qualified BV.Types    as BV
import qualified BV.Canonize as BV
import qualified BV.Util     as BV
import qualified Cudd.Imperative as C
import Solver.SMTSolver
import Abstract.Predicate
import Abstract.BFormula
import Internal.ISpec
import Internal.IExpr
import Internal.IType
import Internal.IVar
import Synthesis.RefineCommon
import Abstract.GroupTag
import Abstract.ACFA2HAST
import Ops
import {-# SOURCE #-} Abstract.MkPredicate
import qualified HAST.BDD as H

type VarMap = M.Map String Term

--------------------------------------------------------------------
-- Normalisation interface
--------------------------------------------------------------------

bvRelNormalise :: (?spec::Spec) => RelOp -> PTerm -> PTerm -> Formula
bvRelNormalise REq  t1 t2 = bvRelNormalise' BV.Eq  t1 t2
bvRelNormalise RNeq _  _  = error "Unexpected '!=' in bvRelNormalise"
bvRelNormalise RLt  t1 t2 = bvRelNormalise' BV.Lt  t1 t2
bvRelNormalise RGt  t1 t2 = bvRelNormalise' BV.Lt  t2 t1
bvRelNormalise RLte t1 t2 = bvRelNormalise' BV.Lte t1 t2
bvRelNormalise RGte t1 t2 = bvRelNormalise' BV.Lte t2 t1

bvRelNormalise' :: (?spec::Spec) => BV.Rel -> PTerm -> PTerm -> Formula
bvRelNormalise' r pt1 pt2 = {-trace ("bvRelNormalise " ++ show pt1 ++ " " ++ show r ++ " " ++ show pt2 ++ " = " ++ show res)-} res 
    where res = fdisj $ map (fconj . map catomToFormula) $ BV.atomToCAtoms a
          st1 = simplifyTopMod $ ptermTerm pt1
          st2 = simplifyTopMod $ ptermTerm pt2
          ((t1', t2'), vmap) = runState (do _t1 <- termToBVTerm st1
                                            _t2 <- termToBVTerm st2
                                            return (_t1, _t2)) M.empty
          a = BV.Atom r t1' t2'
          catomToFormula (BV.CAtom op' ct1 ct2) = 
              let ?vmap = vmap in
              let (pol, pop) = case op' of
                                    BV.Eq  -> (True,  PEq)
                                    BV.Neq -> (False, PEq)
                                    BV.Lt  -> (True,  PLt)
                                    BV.Lte -> (True,  PLte)
                  t1 = ctermToTerm ct1
                  t2 = ctermToTerm ct2
                  (pt1', pt2') = case pt1 of
                                      PTPtr _ -> (PTPtr t1, PTPtr t2)
                                      PTInt _ -> (PTInt t1, PTInt t2) in
              if' pol (FBoolAVar $ AVarPred $ PAtom pop pt1' pt2')
                      (FNot $ FBoolAVar $ AVarPred $ PAtom pop pt1' pt2')


bvTermNormalise :: (?spec::Spec) => Term -> Term
bvTermNormalise t = {-trace ("bvTermNormalise " ++ show t ++ " = " ++ show res)-} res
    where res = let ?vmap = vmap in ctermToTerm ct
          (t', vmap) = runState (termToBVTerm t) M.empty
          ct = BV.termToCTerm t'

--------------------------------------------------------------------
-- Symbolically solving systems of equations and inequalities
--------------------------------------------------------------------

-- Represents a solution of a system of equations.
-- Matches every scalar field of a variable to an expression, 
-- or True if any value is allowed or False if no solution could be
-- found for this variable.
data VarAsn = AsnScalar [((Int,Int), Either Bool Expr)]
            | AsnStruct [(String, VarAsn)]
            deriving (Eq, Show)


-- Solve a system of equations for a subset of variables.
bvSolve :: (?spec::Spec) => [(AbsVar,[Bool])] -> [String] -> [(Expr, [(String, VarAsn)])]
bvSolve asns vs = {-trace ("bvSolve " ++ show vs ++ " " ++ show asns) $-}
    case BV.exTerm qvs atoms of
         Just cas -> let ?vmap = vmap in map (solToVarAsns vmap vs) cas 
         Nothing  -> error $ "bvSolve failed on: " ++ show atoms ++ "\nTest case:\n" ++ test
    where rels = if any (avarIsRelPred . fst) asns
                    then error "bvSolve: cannot handle inductive predicates"
                    else -- TODO: commented out stuff may actually be useful
                         -- resolveAddresses 
                         -- $ resolveIndices 
                         -- $ return $
                         map avarToRel asns
          ((atoms, qvs), vmap) = runState (do _atoms <- mapM relToAtom rels
                                              _qvs   <- mapM mkVar vs
                                              return (_atoms, concat _qvs)) M.empty
          test = "([" ++ (intercalate "," $ map BV.varToHaskell qvs) ++ "], [" ++ 
                         (intercalate ", " $ map BV.atomToHaskell atoms) ++ "])"

solToVarAsns :: (?spec::Spec, ?vmap::VarMap) => VarMap -> [String] -> ([BV.CAtom], [(BV.SVar, Either Bool BV.CTerm)]) -> (Expr, [(String, VarAsn)])
solToVarAsns vmap vs (cond, sol) = (conj $ map (catomToExpr vmap) cond, map (\v -> (v, solToVarAsn sol $ EVar v)) vs)

solToVarAsn :: (?spec::Spec, ?vmap::VarMap) => [(BV.SVar, Either Bool BV.CTerm)] -> Expr -> VarAsn
solToVarAsn sol e = 
    case exprType e of
         Struct _ fs  -> AsnStruct $ map (\(Field n _) -> (n, solToVarAsn sol $ EField e n)) fs
         Array _ _ _  -> error "solToVarAsn: Array is not supported"
         VarArray _ _ -> error "solToVarAsn: VarArray is not supported"
         _            -> solToScalarAsn sol e

solToScalarAsn :: (?spec::Spec, ?vmap::VarMap) => [(BV.SVar, Either Bool BV.CTerm)] -> Expr -> VarAsn
solToScalarAsn sol e = AsnScalar 
    $ sortBy (\((l1,_),_) ((l2,_),_) -> compare l1 l2)
    $ map (\((_,s),v) -> (s, convert v))
    $ filter ((== show e) . BV.vName . fst . fst) sol
    where convert :: Either Bool BV.CTerm -> Either Bool Expr
          convert (Left b)   = Left b
          convert (Right ct) = Right $ fixupType (exprType e) $ termToExpr $ ctermToTerm ct

--------------------------------------------------------------------
-- SMT solver interface
--------------------------------------------------------------------

bvSolver :: RM s u rm => Spec -> SMTSolver -> C.DDManager s u  -> TheorySolver s u AbsVar AbsVar Var rm
bvSolver spec solver m = TheorySolver { unsatCoreState      = bvUnsatCore           spec solver
                                      , unsatCoreStateLabel = bvUnsatCoreStateLabel spec solver
                                      , eQuant              = bvEquantTmp           spec solver m
                                      , getVarsLabel        = let ?spec = spec in (\av -> filter ((==VarTmp) . varCat) $ avarVar av)
                                      }

bvUnsatCore :: Spec -> SMTSolver -> [(AbsVar,[Bool])] -> Maybe [(AbsVar,[Bool])]
bvUnsatCore _ solver ps = 
    case smtGetCore solver $ map (uncurry avarAsnToFormula . mapSnd boolArrToBitsBe) ps of
         Just (Just core) -> Just $ map (ps !!) core
         Just Nothing     -> Nothing
         Nothing          -> error $ "bvUnsatCore: could not solve instance: " ++ show ps

bvUnsatCoreStateLabel :: Spec -> SMTSolver -> [(AbsVar, [Bool])] -> [(AbsVar, [Bool])] -> Maybe ([(AbsVar, [Bool])], [(AbsVar, [Bool])])
bvUnsatCoreStateLabel spec solver sps lps = 
    case bvUnsatCore spec solver (lps++sps) of
         Just core -> let ?spec = spec in Just $ partition ((==VarState) . avarCategory . fst) core
         _         -> Nothing

bvEquantTmp :: RM s u rm => Spec -> SMTSolver -> C.DDManager s u -> [(AbsVar,[Bool])] -> PVarOps pdb s u -> StateT pdb (rm (ST s)) (C.DDNode s u)
bvEquantTmp spec solver m avs ops = 
    let ?spec = spec
    in bvEquant spec solver m ops avs
       $ nub
       $ map varName
       $ filter ((== VarTmp) . varCat) 
       $ concatMap (avarVar . fst) avs

bvEquant :: RM s u rm => Spec -> SMTSolver -> C.DDManager s u -> PVarOps pdb s u -> [(AbsVar,[Bool])] -> [String] -> StateT pdb (rm (ST s)) (C.DDNode s u)
bvEquant spec solver m ops avs vs = do
    let ?spec = spec
    let -- Deal with arrays and pointers. 
        dnf = if any (avarIsRelPred . fst) avs
                 then error "bvEquant: cannot handle inductive predicates"
                 else resolveAddresses 
                      $ resolveIndices 
                      $ return 
                      $ map avarToRel avs
        f  = fdisj $ map (equant' vs solver) dnf
        f' = if' (smtCheckSAT solver [fnot f] == Just False) FTrue f
    H.compileBDD m ops (avarGroupTag . bavarAVar) $ compileFormula {-$ trace ("bvEquant " ++ show vs ++ ". "++ show avs ++ " = " ++ show f') $-} f'

equant' :: (?spec::Spec) => [String] -> SMTSolver -> [(BV.Rel, Term, Term)] -> Formula
equant' vs solver rels = 
    -- Check formula's satisfiability and validity using SMT solver first.
    -- The BV solver only detects unsat and valid formulas in few special cases.
    if' (smtCheckSAT solver forms == Just False)                      FFalse
    $ if' (smtCheckSAT solver [fdisj $ map fnot forms] == Just False) FTrue
    $ case BV.exTerm qvs atoms of
           Just cas -> -- trace ("bvEquant " ++ show atoms ++ "\nTest case:\n" ++ test)
                       fdisj 
                       $ filter (\f -> smtCheckSAT solver [f] /= Just False)
                       $ map (fconj . map (catomToForm vmap) . fst) cas
           Nothing  -> error $ "bvEquant failed on: " ++ show atoms ++ "\nTest case:\n" ++ test                                        
    where forms         = map (\(r, t1, t2) -> ptrFreeBExprToFormula $ EBinOp (bvRelToOp r) (termToExpr t1) (termToExpr t2)) rels
          ((atoms, qvs), vmap) = runState (do _atoms <- mapM relToAtom rels
                                              _qvs   <- mapM mkVar vs
                                              return (_atoms, concat _qvs)) M.empty
          test = "([" ++ (intercalate "," $ map BV.varToHaskell qvs) ++ "], [" ++ 
                         (intercalate ", " $ map BV.atomToHaskell atoms) ++ "])"

mkVar :: (?spec::Spec) => String -> State VarMap [BV.Var]
mkVar n = do
    let scalars = map scalarExprToTerm' $ exprScalars (EVar n) (exprType $ EVar n)
    mapM (\t -> do varMapInsert t
                   return $ BV.Var (show t) (termWidth t)) scalars

--------------------------------------------------------------------
-- Conversion to data structures of the BV library
--------------------------------------------------------------------

-- convert modulo division term to slice without concatenating it with 0
simplifyTopMod :: Term -> Term
simplifyTopMod (TBinOp AMod t1 t2) | isConstTerm t2 && (isPow2 $ ivalVal $ evalConstTerm t2) 
                                   = TSlice t1 (0, (log2 $ ivalVal $ evalConstTerm t2) - 1)
simplifyTopMod t                   = t


varMapInsert :: Term -> State VarMap ()
varMapInsert t = modify (M.insert (show t) t)

avarToRel :: (?spec::Spec) => (AbsVar, [Bool]) -> (BV.Rel, Term, Term)
avarToRel (AVarPred (PAtom op t1 t2), [val])   = case (op, val) of
                                                      (PEq , True ) -> (BV.Eq , ptermTerm t1, ptermTerm t2)
                                                      (PEq , False) -> (BV.Neq, ptermTerm t1, ptermTerm t2)
                                                      (PLt , True ) -> (BV.Lt , ptermTerm t1, ptermTerm t2)
                                                      (PLt , False) -> (BV.Lte, ptermTerm t2, ptermTerm t1)
                                                      (PLte, True ) -> (BV.Lte, ptermTerm t1, ptermTerm t2)
                                                      (PLte, False) -> (BV.Lt , ptermTerm t2, ptermTerm t1)
avarToRel (AVarBool t               , [True])  = (BV.Eq , t, TTrue) 
avarToRel (AVarBool t               , [False]) = (BV.Neq, t, TTrue) 
avarToRel (AVarInt  t               , val)     = (BV.Eq , t, TUInt (length val) (boolArrToBitsBe val))
avarToRel (AVarEnum t               , val)     = (BV.Eq , t, TEnum $ (enumEnums $ getEnumeration n) !! (boolArrToBitsBe val))
                                                 where Enum _ n = termType t

-- TODO: Add pair-wise inequality constraints between
-- AddrOf terms
resolveAddresses :: [[(BV.Rel, Term, Term)]] -> [[(BV.Rel, Term, Term)]]
resolveAddresses = id

-- Identify terms isomorphic up to array indices, e.g.,
-- x[i].field and x[j].field.  Transform the input DNF:
-- (i == j /\ dnf (with i substituted by j)) \/ (i /= j /\ dnf)
-- Every such transformation doubles the size of DNF.
-- Since equation i==j may introduce new isomorphic predicates,
-- continue the process recursively until no new isomorphic pairs
-- can be found.  
-- Hopefully, this nasty piece of logic is sufficient to add 
-- support for array logic to our decision procedure.
resolveIndices :: [[(BV.Rel, Term, Term)]] -> [[(BV.Rel, Term, Term)]]
resolveIndices = resolveIndices' []

resolveIndices' :: [(Term,Term)] -> [[(BV.Rel, Term, Term)]] -> [[(BV.Rel, Term, Term)]]
resolveIndices' iso0 dnf | isNothing miso = dnf
                         | otherwise      = resolveIndices' ((t1,t2):iso0) dnf'
   where miso = listToMaybe
                $ filter (\pair -> not $ elem pair iso0)                          -- ignore pairs that have already been resolved
                $ (concat . mapMaybe termsIsomorphic)                             -- extract pairs of non-matching indices
                $ (pairs . nub)                                                   -- all unique pairs of non-equal terms
                $ concatMap (\(_, t1',t2') -> scalarTerms t1' ++ scalarTerms t2') -- extract all terms with indices from DNF
                $ concat dnf
         Just (t1,t2) = miso
         t1eqt2   = (BV.Eq, t1, t2)
         t1neqt2  = (BV.Neq, t1,t2)
         -- substitute t1 with t2 throughout dnf
         dnfsubst = map (map (\(r, t1', t2') -> (r, subst t1 t2 t1', subst t1 t2 t2'))) dnf
         dnf'     = (map (t1eqt2:) dnfsubst) ++ (map (t1neqt2:) dnf)

subst :: Term -> Term -> Term -> Term
subst old new t                 | t == old = new
subst old new (TAddr t)                    = TAddr $ subst old new t
subst old new (TField t f)                 = TField (subst old new t) f
subst old new (TIndex t i)                 = TIndex (subst old new t) (subst old new i)
subst old new (TUnOp op t)                 = TUnOp op $ subst old new t
subst old new (TBinOp op t1 t2)            = TBinOp op (subst old new t1) (subst old new t2)
subst old new (TSlice t s)                 = TSlice (subst old new t) s
subst old _   _                            = old

-- If terms are isomorphic modulo indices, and at least one index is not a constant,
-- returns all pairs of index expressions that are not equal.
termsIsomorphic :: (Term, Term) -> Maybe [(Term, Term)]
termsIsomorphic (TAddr t1    , TAddr t2)                   = termsIsomorphic (t1, t2)
termsIsomorphic (TField t1 f1, TField t2 f2) | f1 == f2    = termsIsomorphic (t1, t2)
termsIsomorphic (TIndex t1 i1, TIndex t2 i2) | isJust miso = fmap ((fromJust miso) ++ ) $ isoPair i1 i2
                                             where miso = termsIsomorphic (t1, t2)
termsIsomorphic (_,_)                                      = Nothing

isoPair :: Term -> Term -> Maybe [(Term, Term)]
isoPair i1 i2 | i1 == i2                         = Just []
              | isConstTerm i1 && isConstTerm i2 = Nothing -- assumes that all constant expressions were evaluated and are represented by equal constant terms
              | otherwise                        = Just [(i1,i2)]

scalarTerms :: Term -> [Term]
scalarTerms   (TVar _)         = []
scalarTerms   (TSInt _ _)      = []
scalarTerms   (TUInt _ _)      = []
scalarTerms   (TEnum _)        = []
scalarTerms   TTrue            = []
scalarTerms t@(TAddr _)        = [t]
scalarTerms t@(TField _ _)     = [t]
scalarTerms t@(TIndex _ _)     = [t]
scalarTerms   (TUnOp _ t)      = scalarTerms t
scalarTerms   (TBinOp _ t1 t2) = scalarTerms t1 ++ scalarTerms t2
scalarTerms   (TSlice t _)     = scalarTerms t

relToAtom :: (?spec::Spec) => (BV.Rel, Term, Term) -> State VarMap BV.Atom
relToAtom (rel, t1, t2) = do 
    t1' <- termToBVTerm t1
    t2' <- termToBVTerm t2
    return $ BV.Atom rel t1' t2'

termToBVTerm :: (?spec::Spec) => Term -> State VarMap BV.Term
termToBVTerm = termToBVTerm' . termNormaliseIndices

termNormaliseIndices :: (?spec::Spec) => Term -> Term
termNormaliseIndices t@(TVar _)         = t
termNormaliseIndices t@(TSInt _ _)      = t
termNormaliseIndices t@(TUInt _ _)      = t
termNormaliseIndices t@(TEnum _)        = t
termNormaliseIndices t@TTrue            = t
termNormaliseIndices  (TAddr t)         = TAddr $ termNormaliseIndices t
termNormaliseIndices  (TField t f)      = TField (termNormaliseIndices t) f
termNormaliseIndices  (TIndex t i)      = TIndex (termNormaliseIndices t) (bvTermNormalise i)
termNormaliseIndices  (TUnOp op t)      = TUnOp op $ termNormaliseIndices t
termNormaliseIndices  (TBinOp op t1 t2) = TBinOp op (termNormaliseIndices t1) (termNormaliseIndices t2)
termNormaliseIndices  (TSlice t s)      = TSlice (termNormaliseIndices t) s

termToBVTerm' :: (?spec::Spec) => Term -> State VarMap BV.Term
termToBVTerm'   (TSlice t s)             = do t' <- termToBVTerm' t
                                              return $ BV.TSlice t' s
termToBVTerm'   (TBinOp ABConcat t1 t2)  = do t1' <- termToBVTerm' t1
                                              t2' <- termToBVTerm' t2
                                              return $ BV.TConcat [t1',t2'] 
termToBVTerm'   (TBinOp APlus t1 t2)     = do t1' <- termToBVTerm' t1
                                              t2' <- termToBVTerm' t2
                                              let w = max (BV.width t1') (BV.width t2')
                                              return $ BV.TPlus [BV.termExt t1' w, BV.termExt t2' w]
termToBVTerm'   (TBinOp ABinMinus t1 t2) = do t1' <- termToBVTerm' t1
                                              t2' <- termToBVTerm' t2
                                              let w = max (BV.width t1') (BV.width t2')
                                              return $ BV.TPlus [BV.termExt t1' w, BV.TMul ((-1) `BV.mod2` w) t2' w]
termToBVTerm'   (TBinOp AMod t1 t2)      | isConstTerm t2 && (isPow2 $ ivalVal $ evalConstTerm t2) 
                                         = do t1' <- termToBVTerm' t1
                                              return $ BV.termExt (BV.TSlice t1' (0, (log2 $ ivalVal $ evalConstTerm t2) - 1)) (termWidth t1)
termToBVTerm'   (TBinOp AMul t1 t2)      | isConstTerm t1 
                                         = do t2' <- termToBVTerm' t2
                                              return $ BV.TMul ((ivalVal $ evalConstTerm t1) `BV.mod2` w) t2' w
                                         | isConstTerm t2
                                         = do t1' <- termToBVTerm' t1
                                              return $ BV.TMul ((ivalVal $ evalConstTerm t2) `BV.mod2` w) t1' w
                                         where w = max (termWidth t1) (termWidth t2)
termToBVTerm'   (TUnOp AUMinus t)        = do t' <- termToBVTerm' t
                                              let w = termWidth t
                                              return $ BV.TMul ((-1) `BV.mod2` w) t' w
termToBVTerm'   (TUnOp ABNeg t)          = do t' <- termToBVTerm' t
                                              return $ BV.TNeg t'
termToBVTerm'   (TSInt w i)              = return $ BV.tConst i w
termToBVTerm'   (TUInt w i)              = return $ BV.tConst i w
termToBVTerm'   TTrue                    = return $ BV.tConst 1 1
termToBVTerm' t@(TEnum n)                = return $ BV.tConst (toInteger $ enumToInt n) (termWidth t)
termToBVTerm' t@(TVar _)                 = do varMapInsert t
                                              return $ BV.TVar (BV.Var (show t) (termWidth t))
termToBVTerm' t@(TField _ _)             = do varMapInsert t
                                              return $ BV.TVar (BV.Var (show t) (termWidth t))
termToBVTerm' t@(TIndex _ _)             = do varMapInsert t
                                              return $ BV.TVar (BV.Var (show t) (termWidth t))
termToBVTerm' t@(TAddr _)                = do varMapInsert t
                                              return $ BV.TVar (BV.Var (show t) (termWidth t))
termToBVTerm' t                          = error $ "termToBVTerm': term not supported: " ++ show t

--------------------------------------------------------------------
-- Conversion back to our data structures
--------------------------------------------------------------------

catomToExpr :: (?spec::Spec) => VarMap -> BV.CAtom -> Expr
catomToExpr vmap (BV.CAtom rel ct1 ct2) = 
    let ?vmap = vmap in fixupTypes $ EBinOp (bvRelToOp rel) (termToExpr $ ctermToTerm ct1) (termToExpr $ ctermToTerm ct2)

catomToForm :: (?spec::Spec) => VarMap -> BV.CAtom -> Formula
catomToForm vmap ca = ptrFreeBExprToFormula $ catomToExpr vmap ca

bvRelToOp :: BV.Rel -> BOp
bvRelToOp BV.Eq  = Eq
bvRelToOp BV.Neq = Neq
bvRelToOp BV.Lt  = Lt
bvRelToOp BV.Lte = Lte

-- Change integer constants to enums where appropriate
fixupTypes :: (?spec::Spec) => Expr -> Expr
fixupTypes (EBinOp op e1 e2) = EBinOp op (fixupType (exprType e2) e1) (fixupType (exprType e1) e2)

fixupType :: (?spec::Spec) => Type -> Expr -> Expr
fixupType (Enum _ n) e = if' (isConstExpr e) (EConst $ EnumVal $ (enumEnums $ getEnumeration n) !! fromInteger (ivalVal $ evalConstExpr e)) e
fixupType (Bool _)   e = if' (isConstExpr e) (EConst $ BoolVal $ if' ((ivalVal $ evalConstExpr e) == 0) False True) e
fixupType _          e = e

ctermToTerm :: (?spec::Spec, ?vmap::VarMap) => BV.CTerm -> Term
ctermToTerm t@BV.CTerm{..} | null ctVars
                           = bvconstToTerm ctConst
                           | BV.cVal ctConst == 0 && (length ctVars == 1)
                           = ctvarToTerm (BV.width t) (head ctVars)
                           | otherwise
                           = pls $ (map (ctvarToTerm (BV.width t)) ctVars) ++ if' (BV.cVal ctConst == 0) [] [bvconstToTerm ctConst]
    where pls [x]    = x
          pls (x:xs) = (TBinOp APlus x (pls xs))

bvconstToTerm :: BV.Const -> Term
bvconstToTerm BV.Const{..} = TUInt cWidth cVal

ctvarToTerm :: (?spec::Spec, ?vmap::VarMap) => Int -> (Integer, (BV.Var, (Int,Int))) -> Term
ctvarToTerm w (c, (v,(l,h))) = vmul
    where v' = ?vmap M.! (BV.vName v)
          vslice = if' ((l==0) && (h == BV.vWidth v - 1)) v' (TSlice v' (l,h))
          vext = if' (h - l + 1 == w) vslice                                              $
                 if' (h - l + 1 < w)  (TBinOp ABConcat vslice (TUInt (w - (h - l + 1)) 0)) $
                 scalarExprToTerm' $ exprSlice (termToExpr vslice) (0, w - 1)
          vmul = if' (c == 1) vext (TBinOp AMul (TUInt w c) vext)
