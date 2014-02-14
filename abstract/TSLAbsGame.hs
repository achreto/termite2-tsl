{-# LANGUAGE ImplicitParams, ScopedTypeVariables, RecordWildCards, TupleSections #-}

module TSLAbsGame(AbsPriv,
                  tslAbsGame, 
                  tslUpdateAbsVarAST,
                  tslStateLabelConstraintAbs,
                  tslInconsistent,
                  tslUpdateAbs) where

import Data.List
import qualified Data.Map             as M
import Debug.Trace
import Data.Maybe
import Text.PrettyPrint.Leijen.Text
import qualified Data.Text.Lazy       as T
import qualified Data.Graph.Inductive as G
import Control.Monad.Trans.Class
import Control.Monad.State.Lazy
import Control.Monad.ST

import TSLUtil
import Util hiding (trace)
import qualified CuddExplicitDeref as C
import ISpec
import TranSpec
import IExpr
import IVar
import IType
import CFA
import Predicate
import Inline
import qualified Interface   as Abs
import qualified TermiteGame as Abs
import qualified HAST.HAST   as H
import qualified HAST.BDD    as H
import ACFA
import CFA2ACFA
import ACFA2HAST
import AbsRelation
import BFormula
import Cascade
import RefineCommon 
import GroupTag

type AbsPriv = [[AbsVar]]
type PDB pdb s u = StateT AbsPriv (StateT pdb (ST s))

--showRelDB :: AbsPriv -> String
--showRelDB = intercalate "\n" . map (\((r,_),b) -> show (r,b)) . fst

-----------------------------------------------------------------------
-- Interface
-----------------------------------------------------------------------

tslAbsGame :: Spec -> C.STDdManager s u -> TheorySolver s u AbsVar AbsVar Var -> Abs.Abstractor s u AbsVar AbsVar AbsPriv
tslAbsGame spec m ts = Abs.Abstractor { Abs.initialState            = []
                                      , Abs.goalAbs                 = tslGoalAbs                 spec m
                                      , Abs.fairAbs                 = tslFairAbs                 spec m
                                      , Abs.initAbs                 = tslInitAbs                 spec m
                                      , Abs.contAbs                 = tslContAbs                 spec m
                                      , Abs.initialVars             = []
                                      --, gameConsistent  = tslGameConsistent  spec
                                      , Abs.stateLabelConstraintAbs = lift . tslStateLabelConstraintAbs spec m
                                      , Abs.updateAbs               = tslUpdateAbs               spec m ts
                                      --, Abs.filterPromoCandidates   = tslFilterCandidates        spec m
                                      }

tslGoalAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslGoalAbs spec m ops = do
    let ?ops  = ops
    p <- lift pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    lift $ mapM (\g -> do let ast = tranPrecondition ("goal_" ++ (goalName g))  (goalCond g)
                          H.compileBDD m ops (avarGroupTag . bavarAVar) ast)
         $ tsGoal $ specTran spec

tslFairAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u [C.DDNode s u]
tslFairAbs spec m ops = do
    let ?ops  = ops
    p <- lift pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    lift $ mapM (H.compileBDD m ops (avarGroupTag . bavarAVar) . bexprAbstract . fairCond) $ tsFair $ specTran spec

tslInitAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslInitAbs spec m ops = do 
    let ?ops  = ops
    p <- lift pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    let pre   = tranPrecondition "init" (fst $ tsInit $ specTran spec)
        extra = bexprAbstract (snd $ tsInit $ specTran spec)
        res   = H.And pre extra
    lift $ H.compileBDD m ops (avarGroupTag . bavarAVar) res

-- TODO: where should this go?

tslStateLabelConstraintAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> StateT pdb (ST s) (C.DDNode s u)
tslStateLabelConstraintAbs spec m ops = do
    let ?ops    = ops
    p <- pdbPred
    let ?spec   = spec
        ?m      = m
        ?pred   = p
    H.compileBDD ?m ?ops (avarGroupTag . bavarAVar) tslConstraint

tslConstraint :: (?spec::Spec, ?pred::[Predicate]) => TAST f e c
tslConstraint = pre
    where 
    -- magic = compileFormula $ ptrFreeBExprToFormula $ mkContLVar ==> mkMagicVar
    -- precondition of at least one transition must hold   
    pre = H.Disj
          $ mapIdx (\tr i -> tranPrecondition ("pre_" ++ show i) tr) $ (tsUTran $ specTran ?spec) ++ (tsCTran $ specTran ?spec)
    

tslContAbs :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> PDB pdb s u (C.DDNode s u)
tslContAbs spec m ops = do 
    let ?ops  = ops
    p <- lift pdbPred
    let ?spec = spec
        ?m    = m
        ?pred = p
    lift $ H.compileBDD m ops (avarGroupTag . bavarAVar) $ bexprAbstract $ mkContLVar === true

tslUpdateAbs :: Spec -> C.STDdManager s u -> TheorySolver s u AbsVar AbsVar Var -> [(AbsVar,[C.DDNode s u])] -> PVarOps pdb s u -> PDB pdb s u ([C.DDNode s u], C.DDNode s u, C.DDNode s u)
tslUpdateAbs spec m _ avars ops = do
    trace ("tslUpdateAbs " ++ (intercalate "," $ map (show . fst) avars)) $ return ()
    let ?ops    = ops
    p <- lift pdbPred
    let ?spec   = spec
        ?m      = m
        ?pred   = p
--    avarbef <- (liftM $ map bavarAVar) $ Abs.allVars ?ops
    upd <- mapM tslUpdateAbsVar avars
--    avaraft <- (liftM $ map bavarAVar) $ Abs.allVars ?ops
--    let avarnew = S.toList $ S.fromList avaraft S.\\ S.fromList avarbef
    inconsistent <- lift $ tslInconsistent spec m ops
--    inconsistent <- case avarnew of
--                         [] -> return $ C.bzero m
--                         _  -> H.compileBDD m ops (avarGroupTag . bavarAVar)
--                               $ H.Disj 
--                               $ map (absVarInconsistent ts . \(x:xs) -> (x, xs ++ avarbef)) 
--                               $ init $ tails avarnew
--    updwithinc <- lift $ C.band m (last upd) (C.bnot inconsistent)
--    lift $ C.deref m inconsistent
--    lift $ C.deref m (last upd)
--    let upd' = init upd ++ [updwithinc]
    return (upd, inconsistent, {-rel-}C.bone m)

tslInconsistent :: Spec -> C.STDdManager s u -> PVarOps pdb s u -> StateT pdb (ST s) (C.DDNode s u)
tslInconsistent spec m ops = do
    let ?spec = spec
    allvars <- Abs.allVars ops
    let enumcond = H.Disj
                   $ map (\av@(AVarEnum t) -> let Enum tname = typ t
                                              in H.Conj 
                                                 $ mapIdx (\_ i -> H.Not $ H.EqConst (H.NVar $ avarBAVar av) i)
                                                 $ enumEnums $ getEnumeration tname)
                   $ filter avarIsEnum $ map bavarAVar allvars
        contcond = compileFormula $ ptrFreeBExprToFormula $ conj [mkContLVar, neg mkMagicVar]
    H.compileBDD m ops (avarGroupTag . bavarAVar) $ H.Disj [enumcond, contcond]

tslUpdateAbsVar :: (?ops::PVarOps pdb s u, ?spec::Spec, ?m::C.STDdManager s u, ?pred::[Predicate]) => (AbsVar,[C.DDNode s u]) -> PDB pdb s u (C.DDNode s u)
tslUpdateAbsVar (av, n) = trace ("compiling " ++ show av) 
                          $ lift $ H.compileBDD ?m ?ops (avarGroupTag . bavarAVar) $ tslUpdateAbsVarAST (av,n)


tslUpdateAbsVarAST :: (?spec::Spec, ?pred::[Predicate]) => (AbsVar, f) -> TAST f e c
tslUpdateAbsVarAST (av, n) | M.member (show av) (specUpds ?spec) = 
    case av of 
         AVarBool _ -> let cas = casTree 
                                 $ map (\(c,e) -> (ptrFreeBExprToFormula c, CasLeaf $ ptrFreeBExprToFormula e)) 
                                 $ (specUpds ?spec) M.! (show av)
                       in compileFCas cas (H.FVar n)
         AVarEnum _ -> let cas = casTree 
                                 $ (map (\(c,e) -> (ptrFreeBExprToFormula c, CasLeaf $ scalarExprToTerm e)))
                                 $ (specUpds ?spec) M.! (show av)
                       in compileTCas cas (H.FVar n)
         _          -> error "tslUpdateAbsVarAST: not a bool or enum variable"

tslUpdateAbsVarAST (av, n)                                       = H.Disj (unchanged:upds)
    where
    trans = mapIdx (\tr i -> varUpdateTrans (show i) (av,n) tr) $ (tsUTran $ specTran ?spec) ++ (tsCTran $ specTran ?spec)
    (upds, pres) = unzip $ catMaybes trans
    -- generate condition when variable value does not change
    ident = H.EqVar (H.NVar $ avarBAVar av) (H.FVar n)
    unchanged = H.And (H.Conj $ map H.Not pres) ident

tslFilterCandidates :: Spec -> C.STDdManager s u -> [AbsVar] -> PDB pdb s u ([AbsVar], [AbsVar])
tslFilterCandidates _ _ avs = do
   cands <- get
   let (relavs, neutral) = partition avarIsRelPred avs
       cands' = cands ++ [relavs]
       good = map fst
              $ head                                                     -- take the oldest group
              $ sortAndGroup snd                                         -- group based on age
              $ map (\av -> (av, fromJust $ findIndex (elem av) cands')) -- determine the age of each var
              relavs
   -- record the new set of candidates in history
   put cands'
   return (neutral, if' (null relavs) [] good)



----------------------------------------------------------------------------
-- Shared with Spec2ASL
----------------------------------------------------------------------------
 
-- additional constraints over automatic variables
--autoConstr :: (?spec::Spec) => Formula
--autoConstr = fconj $ map ptrFreeBExprToFormula $ [nolepid, notag]
--    where 
--    -- $cont  <-> $lepid == $nolepid
--    nolepid = EBinOp Or (EBinOp And mkContLVar (EBinOp Eq mkEPIDLVar (EConst $ EnumVal mkEPIDNone)))
--                        (EBinOp And (EUnOp Not mkContLVar) (EBinOp Neq mkEPIDLVar (EConst $ EnumVal mkEPIDNone)))
--    -- !$cont <-> $tag == $tagnone
--    notag   = EBinOp Or (EBinOp And (EUnOp Not mkContLVar) (EBinOp Eq mkTagVar (EConst $ EnumVal mkTagNone)))
--                        (EBinOp And mkContLVar             (EBinOp Neq mkTagVar (EConst $ EnumVal mkTagNone)))

----------------------------------------------------------------------------
-- PDB operations
----------------------------------------------------------------------------

pdbPred :: (?ops::PVarOps pdb s u) => StateT pdb (ST s) [Predicate]
pdbPred = do
    bavars <- Abs.allVars ?ops
    return $ map (\(AVarPred p) -> p)
           $ filter avarIsPred 
           $ map bavarAVar bavars

----------------------------------------------------------------------------
-- Precomputing inconsistent combinations of abstract variables
----------------------------------------------------------------------------

absVarInconsistent :: (?spec::Spec, ?m::C.STDdManager s u) => TheorySolver s u AbsVar AbsVar Var -> (AbsVar, [AbsVar]) -> TAST f e c
absVarInconsistent ts (AVarPred p, avs) = 
    case predVar p of
         [v] -> -- consider pair-wise combinations with all predicates involving only this variable;
                -- only consider positive polarities (does it make sense to try both?)
                compileFormula
                $ fdisj
                $ map (\p' -> let f = ptrFreeBExprToFormula $ predToExpr p `land` predToExpr p' in
                              case (unsatCoreState ts) [(AVarPred p, [True]), (AVarPred p', [True])] of
                                   Just _ -> f
                                   _      -> FFalse)
                $ filter (\p' -> p' /= p && predVar p' == predVar p) 
                $ map (\(AVarPred p') -> p') 
                $ filter avarIsPred avs
         _   -> H.F

--absVarInconsistent _ (AVarEnum t) = H.F -- enum must be one of legal value
absVarInconsistent _ _            = H.F

----------------------------------------------------------------------------
-- Predicate/variable update functions
----------------------------------------------------------------------------

bexprAbstract :: (?spec::Spec, ?pred::[Predicate]) => Expr -> TAST f e c
bexprAbstract = compileFormula . bexprToFormula

-- Compute precondition of transition without taking prefix blocks and wires into account
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => String -> Transition -> TAST f e c
tranPrecondition trname Transition{..} = varUpdateLoc trname [] tranFrom (cfaLocInlineWirePrefix ?spec tranCFA tranFrom)

-- Compute update function for an abstract variable wrt to a transition
-- Returns update function and precondition of the transition.  The precondition
-- can be used to generate complementary condition when variable value remains 
-- unchanged.  
varUpdateTrans :: (?spec::Spec, ?pred::[Predicate]) => String -> (AbsVar,f) -> Transition -> Maybe (TAST f e c, TAST f e c)
varUpdateTrans trname (av,nxt) Transition{..} = if all G.isEmpty cfas'
                                                   then Nothing
                                                   else Just (H.Conj upds, H.Disj pres)
    where -- list all rules for the relation
          vexps = (avarToExpr av) : 
                  (case av of
                        AVarPred p@PRel{..} -> snd $ instantiateRelation (getRelation pRel) pArgs
                        _                   -> [])
          (upds, pres, cfas') = unzip3
                                $ map (\e -> let cfa' = pruneCFAVar [e] tranCFA
                                                 cfa  = cfaLocInlineWirePrefix ?spec cfa' tranFrom
                                                 pre  = varUpdateLoc (trname ++ "_pre") [] tranFrom cfa
                                                 upd  = varUpdateLoc trname [((av, e), nxt)] tranFrom cfa
                                             in (upd, pre, cfa'))
                                  vexps


-- Compute update functions for a list of variables for a location inside
-- transition CFA. 
varUpdateLoc :: (?spec::Spec, ?pred::[Predicate]) => String -> [((AbsVar, Expr), f)] -> Loc -> CFA -> TAST f e c
varUpdateLoc trname vs loc cfa = acfaTraceFile acfa ("acfa_" ++ trname ++ "_" ++ vlst)
                                 $ traceFile ("HAST for " ++ vlst ++ ":\n" ++ show ast') (trname ++ "-" ++ vlst ++ ".ast") ast
    where
    acfa = tranCFAToACFA (map fst vs) loc cfa
    avs  = map (\((av,_),nxt) -> (av, nxt)) vs
    ast  = compileACFA avs acfa
    vs'  = map (\(av,_) -> (av, text $ T.pack $ show av ++ "'")) avs
    vlst = intercalate "_" $ map (show . snd) vs'
    ast'::(TAST Doc Doc Doc) = compileACFA vs' acfa
