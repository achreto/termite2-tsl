{-# LANGUAGE ImplicitParams, RecordWildCards, TemplateHaskell, ConstraintKinds, FlexibleContexts #-}

module CodeGen.AbsSim (CompiledMB,
               simulateCFAAbstractToLoc,
               simulateCFAAbstractToCompletion,
               simulateGameAbstract,
               simulateControllable,
               restrictToMB,
               compileExpr) where

import Data.List
import Data.Maybe
import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Monad.State
import Control.Monad.ST
import Control.Monad.Morph

import Util
import Internal.PID
import Synthesis.Resource
import Synthesis.RefineCommon
import Synthesis.Interface
import Synthesis.TermiteGame
import Synthesis.BddRecord
import Synthesis.BddUtil
import Internal.ISpec hiding (getVar)
import Abstract.Predicate
import Internal.TranSpec
import Abstract.TSLAbsGame
import Abstract.GroupTag
import Abstract.ACFA2HAST
import Internal.CFA
import Pos
import Synthesis.CG
import Frontend.Inline
import Abstract.BFormula
import qualified Internal.IExpr    as I
import qualified Cudd.Imperative   as C
import qualified HAST.HAST         as H
import qualified HAST.BDD          as H


----------------------------------------------------------
-- Type
----------------------------------------------------------

type CompiledMB      = (Pos, CFA)
type CompiledMB' s u = (DDNode s u, CFA)

type DbgNotify s u = (String -> DDNode s u -> DDNode s u -> DDNode s u -> ST s ())

----------------------------------------------------------
-- Interface
----------------------------------------------------------

-- Generate condition that holds whenever the magic block specified by 
-- mbpos is active.
mbToStateConstraint :: (RM s u t) => Spec -> C.DDManager s u -> DB s u AbsVar AbsVar -> Pos -> t (ST s) (DDNode s u)
mbToStateConstraint spec m pdb mbpos = do
    let Ops{..} = constructOps m
    let ?spec = spec
        ?m    = m
        ?db   = pdb
    let mblocs = specLookupMB spec mbpos
    compileExpr $ I.conj [mkMagicVar, I.disj $ map (\(pid, mbloc, _) -> let cfa = specGetCFA spec (EPIDProc pid) 
                                                                            in mkPCEq cfa pid (mkPC pid mbloc)) 
                                                   mblocs]

-- Restrict a relation to states inside the MB
restrictToMB :: (RM s u t) => Spec -> C.DDManager s u -> DB s u AbsVar AbsVar -> Pos -> DDNode s u -> t (ST s) (DDNode s u)
restrictToMB spec m pdb mbpos set = do
    let ops@Ops{..} = constructOps m
    cond <- mbToStateConstraint spec m pdb mbpos
    res <- $r2 band cond set
    $d deref cond
    return res

-- Abstractly simulate CFA consisting of controllable transitions from 
-- initial location to the specified pause location.
simulateCFAAbstractToLoc :: (RM s u t) 
                         => Spec 
                         -> C.DDManager s u 
                         -> RefineDynamic s u 
                         -> DB s u AbsVar AbsVar 
                         -> DDNode s u 
                         -> Lab s u 
                         -> CFA 
                         -> DDNode s u 
                         -> Loc 
                         -> DDNode s u
                         -> DbgNotify s u 
                         -> t (ST s) (Maybe (DDNode s u))
simulateCFAAbstractToLoc spec m refdyn pdb cont lp cfa initset loc winregion cb = do
    let ?m    = m
        ?spec = spec
        ?db   = pdb
        ?rd   = refdyn
        ?cont = cont
        ?lp   = lp
        ?cb   = cb
        ?winregion = winregion
    let Ops{..} = constructOps ?m
    annot <- cfaAnnotateReachable cfa initset
    res <- maybe (return Nothing)
                 (\rel -> do $rp ref rel
                             return $ Just rel)
                 (M.lookup loc annot)
    mapM_ ($d deref) $ M.elems annot
    return res

-- Abstractly simulate controllable CFA to completion.  
-- Return the set of final states.
simulateCFAAbstractToCompletion :: (RM s u t) 
                                => Spec 
                                -> C.DDManager s u 
                                -> RefineDynamic s u 
                                -> DB s u AbsVar AbsVar 
                                -> DDNode s u 
                                -> Lab s u 
                                -> CFA 
                                -> DDNode s u 
                                -> DDNode s u
                                -> DbgNotify s u 
                                -> t (ST s) (DDNode s u)
simulateCFAAbstractToCompletion spec m refdyn pdb cont lp cfa initset winregion cb = do
    let ops@Ops{..} = constructOps m
    let ?m    = m
        ?spec = spec
        ?db   = pdb
        ?rd   = refdyn
        ?cont = cont
        ?lp   = lp
        ?cb   = cb
        ?winregion = winregion
    annot <- cfaAnnotateReachable cfa initset
    let finalsets = mapMaybe (\loc -> M.lookup loc annot) $ cfaFinal cfa
    res <- $r $ disj ops finalsets
    mapM_ ($d deref) $ M.elems annot
    return res

-- Simulate the entire game starting from the initial set. Include 
-- completely implemented magic blocks in the simulation.  Returns the set
-- of reachable states.
simulateGameAbstract :: (RM s u t) 
                     => Spec 
                     -> C.DDManager s u 
                     -> RefineDynamic s u 
                     -> DB s u AbsVar AbsVar 
                     -> DDNode s u 
                     -> Lab s u 
                     -> [CompiledMB] 
                     -> DDNode s u 
                     -> DDNode s u
                     -> DbgNotify s u 
                     -> t (ST s) (DDNode s u)
simulateGameAbstract spec m refdyn pdb@DB{_symbolTable = SymbolInfo{..}, _sections = SectionInfo{..}, ..} cont lp mbs initset' winregion cb = do
    let ops@Ops{..} = constructOps m
    let ?m    = m
        ?spec = spec
        ?rd   = refdyn
        ?db   = pdb
        ?cont = cont
        ?lp   = lp
        ?cb   = cb
        ?winregion = winregion
    initset'' <- $r2 band initset' (bnot $ inconsistentInit ?rd)
    -- Compute the set of initial states
    let initvs = (concatMap sel1 $ M.elems _initVars) \\ (concatMap sel1 $ M.elems _stateVars)
    initcube <- $r $ nodesToCube initvs
    init0 <- $r2 bexists initcube initset''
    $d deref initset''
    $d deref initcube
    initset <- $r1 (bexists _untrackedCube) init0
    $d deref init0
    checkWinRegion ops winregion initset' "simulateGameAbstract: initset' is not a subset of the winning region"
    -- Compute magic block constraints
    mbs' <- mapM (\(p, cfa) -> do cond <- mbToStateConstraint spec m pdb p
                                  return (cond, cfa)) mbs
    -- Start fix point computation from this set
    res <- simulateGameAbstractFrom mbs' initset
    mapM_ ($d deref . fst) mbs'
    return res


----------------------------------------------------------
-- Internals
----------------------------------------------------------

checkWinRegion :: (RM s u t) => Ops s u -> DDNode s u -> DDNode s u -> String -> t (ST s) ()
checkWinRegion Ops{..} win set txt = do
    issubset <- lift $ leq set win
    when (not issubset) $ lift $ traceST txt

-- Simulate the entire game starting from the given set.
simulateGameAbstractFrom :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u, ?winregion::DDNode s u, ?cb::DbgNotify s u) 
                         => [CompiledMB' s u] 
                         -> DDNode s u 
                         -> t (ST s) (DDNode s u)
simulateGameAbstractFrom mbs initset = do
    let ops@Ops{..} = constructOps ?m
        RefineDynamic{..} = ?rd
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
    -- transitive closure of uncontrollable from initset
    reach <- applyUncontrollableTC ops (SynthData sinfo trans ?cont ?rd ?lp) initset
    checkWinRegion ops ?winregion reach "simulateGameAbstractFrom: reach is not a subset of the winning region"
    -- simulate magic blocks
    deltas <- mapM (\(cond, cfa) -> do bef <- $r2 band cond reach
                                       aft <- simulateCFAAbstractToCompletion ?spec ?m ?rd ?db ?cont ?lp cfa bef ?winregion ?cb
                                       $d deref bef
                                       aft' <- clearMagic aft
                                       $d deref aft
                                       return aft')
                   mbs
    -- add new sets
    reach' <- $r $ disj ops $ reach:deltas
    mapM_ ($d deref) $ reach:deltas
    done <- lift $ leq reach' initset
    $d deref initset
    -- repeat unless fixed point reached
    if done
       then return reach'
       else simulateGameAbstractFrom mbs reach'

-- Takes a set of states and forces the magic variable to false.
clearMagic :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> t (ST s) (DDNode s u)
clearMagic set = do
    let Ops{..} = constructOps ?m
        DB{_symbolTable = SymbolInfo{..}, ..} = ?db
    magcube <- $r $ nodesToCube $ sel1 $ _stateVars M.! (AVarBool $ TVar mkMagicVarName)
    set' <- $r2 bexists magcube set
    $d deref magcube
    nmagic <- compileExpr $ I.neg mkMagicVar
    res <- $r2 band set' nmagic
    $d deref nmagic
    $d deref set'
    return res

compileExpr :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) => I.Expr -> t (ST s) (DDNode s u)
compileExpr e = do
     let Ops{..} = constructOps ?m
     (res, CompileState newvars _) <- 
         (flip runStateT) (CompileState (NewVars []) ?db) 
         $ H.compileBDD ?m (compileOps $ constructOps ?m) (avarGroupTag . bavarAVar) 
         $ compileFormula 
         $ ptrFreeBExprToFormula e
     if null $ _allocatedStateVars newvars
        then return ()
        else error $ "compileExpr " ++ show e ++ " created new variables"
     $r $ return res

-- Simulate a controllable transition tr from "from" followed by a transitive 
-- closure of uncontrollable transitions.
-- Assumes that label variables and don't cares in tr.
simulateControllable :: (RM s u t, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u, ?winregion::DDNode s u, ?cb::DbgNotify s u) 
                     => DDNode s u 
                     -> DDNode s u 
                     -> t (ST s) (DDNode s u)
simulateControllable from tr = do
    -- E x, u, l . tr & from & c+c
    let ops@Ops{..} = constructOps ?m
        RefineDynamic{..} = ?rd
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
    trfrom  <- $r2 band tr from
    trfromc0 <- $r2 band trfrom consistentPlusCULCont
    $d deref trfrom
    trfromc1 <- $r1 (bexists _trackedCube) trfromc0
    $d deref trfromc0
    trfromc2 <- $r1 (bexists _untrackedCube) trfromc1
    $d deref trfromc1
    trfromc3 <- $r1 (bexists _outcomeCube) trfromc2
    $d deref trfromc2
    to' <- $r1 (bexists _labelCube) trfromc3
    $d deref trfromc3
    to <- $r1 mapVars to'
    $d deref to'
    checkWinRegion ops ?winregion to $ "simulateControllable: controllable transition leaves winning region"

--    issubset <- lift $ leq to ?winregion
--    when (not issubset) $ lift $ ?cb "simulateControllable" from tr to

    totc <- applyUncontrollableTC ops (SynthData sinfo trans ?cont ?rd ?lp) to
    $d deref to
    return totc


-- Annotate pause locations with sets of states
-- initset - set of possible initial states
-- Assumes that pause locations that represent magic blocks do not have outgoing transitions.
cfaAnnotateReachable :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u, ?winregion::DDNode s u, ?cb::DbgNotify s u) 
                     => CFA 
                     -> DDNode s u 
                     -> t (ST s) (M.Map Loc (DDNode s u))
cfaAnnotateReachable cfa initset = do
    let Ops{..} = constructOps ?m
    $rp ref initset
    -- decompose into transitions; ignore transitions from MBs
    let states = filter (not . isMBLoc cfa) {-$ cfaTraceFile cfa "cfaAnnotateReachable"-} $ cfaDelayLocs cfa
        tcfas = concatMap (cfaLocTrans cfa) states
    -- compile transitions
    tupds <- mapM (\(to, tcfa) -> do let from = head $ cfaSource tcfa
                                         sink = head $ cfaSink   tcfa
                                     upd <- compileTransition (Transition from sink tcfa)
                                     return (from, to, upd))
                  tcfas
    res <- annotate' tupds [cfaInitLoc] (M.singleton cfaInitLoc initset) 
    mapM_ ($d deref . sel3) tupds
    return res

annotate' :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db :: DB s u AbsVar AbsVar, ?cont::DDNode s u, ?lp::Lab s u, ?winregion::DDNode s u, ?cb::DbgNotify s u)
          => [(Loc, Loc, DDNode s u)]    -- Compiled transitions
          -> [Loc]                       -- Frontier
          -> M.Map Loc (DDNode s u)      -- Annotations computed so far
          -> t (ST s) (M.Map Loc (DDNode s u))
annotate' _    []          annot = return annot
annotate' upds (loc:front) annot = do
    let ops@Ops{..} = constructOps ?m
    -- transitions from loc
    (front'', annot'') <- foldM (\(front', annot') (_, to, upd) -> do 
                                   nxt <- simulateControllable (annot' M.! loc) upd
                                   checkWinRegion ops ?winregion nxt $ "annotate': transition from " ++ show loc ++ " to " ++ show to ++ " leaves winning region"
                                   -- If new reachable states have been discovered in to, 
                                   -- annotate to with these states and add it to the frontier
                                   case M.lookup to annot' of
                                      Nothing  -> return (to:front', M.insert to nxt annot')
                                      Just ann -> do issubset <- lift $ leq nxt ann
                                                     if issubset
                                                        then do $d deref nxt
                                                                return (front', annot')
                                                        else do newannot <- $r2 bor nxt ann
                                                                $d deref nxt
                                                                $d deref ann
                                                                return (to:front', M.insert to newannot annot'))
                          (front, annot)
                          $ filter ((== loc) . sel1) upds
    annotate' upds front'' annot''

-- State maintained when compiling a transition.
-- _cnv collects new untracked predicates to be quantified away after compilation.
data CompileState s u sp lp = CompileState {
    _cnv :: NewVars s u sp,
    _cdb :: DB s u sp lp
}
--makeLenses ''CompileState

liftToCompileState :: StateT (DB s u sp lp) (ST s) a -> StateT (CompileState s u sp lp) (ST s) a
liftToCompileState (StateT func) = StateT $ \st -> do
    (res, st') <- func (_cdb st) 
    return (res, CompileState (_cnv st) st')

withTmpCompile' :: Ops s u -> (DDNode s u -> StateT (CompileState s u sp lp) (ST s) a) -> StateT (CompileState s u sp lp) (ST s) a
withTmpCompile' Ops{..} func = do
    ind <- liftToCompileState allocIdx
    var <- lift $ ithVar ind
    res <- func var
    liftToCompileState $ freeIdx ind
    lift $ deref var
    return res


compileTransition :: (RM s u t, ?db::DB s u AbsVar AbsVar, ?spec::Spec, ?m::C.DDManager s u) => Transition -> t (ST s) (DDNode s u)
compileTransition t = do
    let DB{_symbolTable = SymbolInfo{..}, _sections = SectionInfo{..}, ..} = ?db
    let ops@Ops{..} = constructOps ?m
    let ?ops = compileOps ops
    let trname = ("from" ++ show (tranFrom t) ++ "to" ++ show (tranTo t))
    let svars = map (\(av, (_, _, d', _)) -> (av, d'))
                $ filter (\(_, (_, is, _, _)) -> not $ null $ intersect is _trackedInds) 
                $ M.toList _stateVars
    (upd_, CompileState newvars _) <- (flip runStateT) (CompileState (NewVars []) ?db) $ do
          p <- hoist lift pdbPred
          let ?pred = p
          let pre = tranPrecondition True trname t
              ast = H.Conj $ pre : (map (compileTransitionVar t) $ svars)
          H.compileBDD ?m ?ops (avarGroupTag . bavarAVar) ast
    upd <- $r $ return upd_
    if null $ _allocatedStateVars newvars
       then return ()
       else lift $ traceST "compileTransition created new variables"
    cube <- $r $ nodesToCube $ concatMap snd $ _allocatedStateVars newvars
    upd' <- $r2 bexists cube upd
    $d deref upd
    $d deref cube
    return upd'
    

allocTmpUntracked :: (Ord sp, Show sp) => Ops s u -> sp -> Int -> Maybe String -> StateT (CompileState s u sp lp) (ST s) [DDNode s u]
allocTmpUntracked ops var size grp = do
    CompileState{..} <- get
    case lookup var $ _allocatedStateVars _cnv of
         Just nodes -> return nodes
         Nothing    -> do lift $ traceST $ "allocating new untracked variable " ++ show var
                          (nodes, _) <- liftToCompileState $ allocN ops size grp
                          put $ CompileState (NewVars $ (var, nodes) : _allocatedStateVars _cnv) _cdb
                          return nodes

compileOps :: (Ord sp, Ord lp, Show lp, Show sp) => Ops s u -> VarOps (CompileState s u sp lp) (BAVar sp lp) s u
compileOps ops = VarOps {withTmp = withTmpCompile' ops, allVars = liftToCompileState allVars', ..}
    where
    getVar (StateVar var size) grp = do
        SymbolInfo{..} <- gets (_symbolTable . _cdb)
        findWithDefaultM sel1 var _stateVars (allocTmpUntracked ops var size grp)
    getVar (LabelVar var _)    _ = do
        SymbolInfo{..} <- gets (_symbolTable . _cdb)
        findWithDefaultM sel1 var _labelVars (error $ "Requested unknown label variable " ++ show var ++ " when compiling controllable CFA")

compileTransitionVar :: (?spec::Spec, ?pred::[Predicate]) => Transition -> (AbsVar, f) -> TAST f e c
compileTransitionVar t (av, n) = maybe ident
                                       (\(upd, pre) -> let unchanged = H.And (H.Not pre) ident
                                                       in H.Or upd unchanged)
                                       (varUpdateTrans (show av) (av,n) t)
    where ident = H.EqVar (H.NVar $ avarBAVar av) (H.FVar n)
