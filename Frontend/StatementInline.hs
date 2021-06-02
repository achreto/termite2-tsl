{-# LANGUAGE ImplicitParams, TupleSections #-}

module Frontend.StatementInline(statSimplify, 
                       statAddNullTypes,
                       procStatToCFA) where

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Traversable as Tr

import Util hiding (name,trace)
import Frontend.Inline
import Frontend.Spec
import Pos
import Name
import Frontend.NS
import Frontend.Statement
import Frontend.Expr
import Frontend.TVar
import Frontend.Method
import Frontend.Type
import Frontend.TypeOps
import Frontend.ExprOps
import Frontend.ExprInline
import Internal.PID

import qualified Internal.IExpr as I
import qualified Internal.CFA   as I
import qualified Internal.IVar  as I
import qualified Internal.ISpec as I
import qualified Internal.IType as I

statSimplify :: (?spec::Spec, ?scope::Scope) => Statement -> NameGen Statement
statSimplify s = (liftM $ sSeq (pos s) (stLab s)) $ statSimplify' s

statSimplify' :: (?spec::Spec, ?scope::Scope) => Statement -> NameGen [Statement]
statSimplify' (SVarDecl p _ v) = 
    case varInit v of
         Just e  -> do asn <- statSimplify' $ SAssign p Nothing (ETerm (pos $ varName v) [varName v]) e
                       return $ (SVarDecl p Nothing v) : asn
         Nothing -> return [SVarDecl p Nothing v]

statSimplify' (SReturn p _ (Just e)) = do
    (ss,e') <- exprSimplify e
    return $ ss ++ [SReturn p Nothing (Just e')]

statSimplify' (SSeq     p _ ss)           = (liftM $ return . SSeq p Nothing) $ mapM statSimplify ss
statSimplify' (SPar     p _ ss)           = (liftM $ return . SPar p Nothing) $ mapM statSimplify ss
statSimplify' (SForever p _ s)            = (liftM $ return . SForever p Nothing) $ statSimplify s
statSimplify' (SDo      p _ b c)          = do (ss,c') <- exprSimplify c
                                               b'      <- statSimplify b
                                               return [SDo p Nothing (sSeq (pos b) Nothing (b':ss)) c']
statSimplify' (SWhile   p _ c b)          = do (ss,c') <- exprSimplify c
                                               b'      <- statSimplify b
                                               return $ ss ++ [SWhile p Nothing c' (sSeq (pos b) Nothing (b':ss))]
statSimplify' (SFor     p _ (mi, c, s) b) = do i' <- case mi of
                                                          Nothing -> return []
                                                          Just i  -> (liftM return) $ statSimplify i
                                               (ss,c') <- exprSimplify c
                                               s' <- statSimplify s
                                               b' <- statSimplify b
                                               return $ i' ++ ss ++ [SFor p Nothing (Nothing, c',s') (sSeq (pos b) Nothing (b':ss))]
statSimplify' (SChoice  p _ ss)           = liftM (return . SChoice p Nothing) $ mapM statSimplify ss
statSimplify' (SInvoke  p _ mref mas)     = -- Order of argument evaluation is undefined in C;
                                            -- Go left-to-right
                                            do (ss, as') <- liftM unzip $ mapM (maybe (return ([], Nothing)) ((liftM $ mapSnd Just) . exprSimplify)) mas
                                               return $ (concat ss) ++ [SInvoke p Nothing mref as']
statSimplify' (SWait    p _ c)            = do (ss,c') <- exprSimplify c
                                               return $ case ss of
                                                             [] -> [SWait p Nothing c']
                                                             _  -> (SPause p Nothing) : (ss ++ [SAssume p Nothing c'])
statSimplify' (SAssert  p _ c)            = do (ss,c') <- exprSimplify c
                                               return $ ss ++ [SAssert p Nothing c']
statSimplify' (SAssume  p _ c)            = do (ss,c') <- exprSimplify c
                                               return $ ss ++ [SAssume p Nothing c']
statSimplify' (SAssign  p _ l r)          = -- Evaluate lhs first
                                            do (ssl,l') <- exprSimplify l
                                               ssr <- exprSimplifyAsn p l' r
                                               return $ ssl ++ ssr
statSimplify' (SITE     p _ c t me)       = do (ss,c') <- exprSimplify c
                                               t'      <- statSimplify t
                                               me'     <- Tr.sequence $ fmap statSimplify me
                                               return $ ss ++ [SITE p Nothing c' t' me']
statSimplify' (SCase    p _ c cs md)      = -- Case labels must be side-effect-free, so it is ok to 
                                            -- evaluate them in advance
                                            do (ssc,c')      <- exprSimplify c
                                               (sscs,clabs') <- (liftM unzip) $ mapM exprSimplify (fst $ unzip cs)
                                               cstats        <- mapM statSimplify (snd $ unzip cs)
                                               md'           <- Tr.sequence $ fmap statSimplify md
                                               return $ concat sscs ++ ssc ++ [SCase p Nothing c' (zip clabs' cstats) md']
statSimplify' st                          = return [st{stLab = Nothing}]


----------------------------------------------------------
-- Convert statement to CFA
----------------------------------------------------------
statToCFA :: (?spec::Spec, ?procs::[I.Process], ?nestedmb::Bool, ?xducer::Bool) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA before s = do
    when (isJust $ stLab s) $ ctxPushLabel (sname $ fromJust $ stLab s)
    after <- statToCFA0 before s
    when (isJust $ stLab s) ctxPopLabel
    return after
    
statToCFA0 :: (?spec::Spec, ?procs::[I.Process], ?nestedmb::Bool, ?xducer::Bool) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA0 before   (SSeq _ _ ss)    = foldM statToCFA before ss
statToCFA0 before s@(SIn _ _ l r)    = do sc <- gets ctxScope
                                          let ?scope = sc
                                          li <- exprToIExprDet l
                                          ri <- exprToIExprDet r
                                          ctxLocSetAct before (I.ActStat s) 
                                          ctxIn before li ri (I.ActStat s)
statToCFA0 before s@(SOut _ _ l r)   = do sc <- gets ctxScope
                                          let ?scope = sc
                                          let SeqSpec _ t = tspec $ typ' $ exprType r
                                          li <- exprToIExpr l t
                                          ri <- exprToIExprDet r
                                          ctxLocSetAct before (I.ActStat s) 
                                          ctxInsTrans' before $ I.TranStat $ I.SOut li ri
statToCFA0 before s@(SPause _ _)     = do ctxLocSetAct before (I.ActStat s)
                                          ctxPause before I.true (I.ActStat s)
statToCFA0 before s@(SWait _ _ c)    = do ctxLocSetAct before (I.ActStat s)
                                          ci <- exprToIExprDet c
                                          ctxPause before ci (I.ActStat s)
statToCFA0 before s@(SStop _ _)      = do ctxLocSetAct before (I.ActStat s)
                                          ctxFinal before
statToCFA0 before   (SVarDecl _ _ v) | isJust (varInit v) = return before
statToCFA0 before   (SVarDecl _ _ v) | otherwise = do 
                                          sc <- gets ctxScope
                                          let ?scope = sc
                                          let scalars = exprScalars $ ETerm nopos [name v]
                                          foldM (\loc e -> do e' <- exprToIExprDet e
                                                              let val = case tspec $ typ' $ exprType e of
                                                                             BoolSpec _    -> I.BoolVal False
                                                                             UIntSpec _ w  -> I.UIntVal w 0
                                                                             SIntSpec _ w  -> I.SIntVal w 0
                                                                             EnumSpec _ es -> I.EnumVal $ sname $ head es
                                                                             PtrSpec  _ t  -> I.NullVal $ mkType $ Type sc t
                                                              ctxInsTrans' loc $ I.TranStat $ e' I.=: I.EConst val)
                                                before scalars
statToCFA0 before s@stat             = do ctxLocSetAct before (I.ActStat s)
                                          after <- ctxInsLoc
                                          statToCFA' before after stat
                                          return after

-- Only safe to call from statToCFA.  Do not call this function directly!
statToCFA' :: (?spec::Spec, ?procs::[I.Process], ?nestedmb::Bool, ?xducer::Bool) => I.Loc -> I.Loc -> Statement -> State CFACtx ()
statToCFA' before _ (SReturn _ _ rval) = do
    -- add transition before before to return location
    mlhs  <- gets ctxLHS
    ret   <- gets ctxRetLoc
    case rval of 
         Nothing -> ctxInsTrans before ret I.TranReturn
         Just v  -> case mlhs of
                         Nothing  -> ctxInsTrans before ret I.TranReturn
                         Just lhs -> do
                            --sc@(ScopeMethod _ m) <- gets ctxScope
                            sc <- gets ctxScope
                            let (ScopeMethod _ m) = sc
                                        let t = fromJust $ methRettyp m
                                        vi <- exprToIExprs v t
                                        let asns = map I.TranStat
                                                   $ zipWith I.SAssign (I.exprScalars lhs (mkType $ Type sc t))
                                                                       (concatMap (uncurry I.exprScalars) vi)
                                        aftargs <- ctxInsTransMany' before asns
                                        ctxInsTrans aftargs ret I.TranReturn

statToCFA' before after s@(SPar _ _ ps) = do
    Just (EPIDProc pid) <- gets ctxEPID
    -- child process pids
    let pids  = map (childPID pid . sname . fromJust . stLab) ps
    -- enable child processes
    aften <- ctxInsTransMany' before $ map (\pid' -> I.TranStat $ mkEnVar pid' Nothing I.=: I.true) pids
    let mkFinalCheck n = I.disj $ map (\loc -> mkPCEq pcfa pid' (mkPC pid' loc)) $ I.cfaFinal pcfa
                         where pid' = childPID pid n
                               p = fromJustMsg ("mkFinalCheck: process " ++ show pid' ++ " unknown") 
                                   $ find ((== n) . I.procName) ?procs
                               pcfa = I.procCFA p
    -- pause and wait for all of them to reach final states
    aftwait <- ctxPause aften (I.conj $ map (mkFinalCheck . sname . fromJust . stLab) ps) (I.ActStat s)
    -- Disable forked processes and bring them back to initial states
    aftreset <- ctxInsTransMany' aftwait $ map (\st -> let n = sname $ fromJust $ stLab st
                                                           pid' = childPID pid n
                                                           pcfa = I.procCFA $ fromJust $ find ((== n) . I.procName) ?procs
                                                       in mkPCAsn pcfa pid' (mkPC pid' I.cfaInitLoc)) ps
    aftdisable <- ctxInsTransMany' aftreset $ map  (\pid' -> I.TranStat $ mkEnVar pid' Nothing I.=: I.false) pids
    ctxInsTrans aftdisable after I.TranNop

statToCFA' before after (SForever _ _ stat) = do
    ctxPushBrkLoc after
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    -- loc' = end of loop body
    loc' <- statToCFA loopback stat
    -- loop-back transition
    ctxInsTrans loc' loopback I.TranNop
    ctxPopBrkLoc

statToCFA' before after (SDo _ _ stat cond) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    ctxPushBrkLoc after
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    aftbody <- statToCFA loopback stat
    ctxLocSetAct aftbody (I.ActExpr cond)
    ctxPopBrkLoc
    -- loop-back transition
    ctxInsTrans aftbody loopback (I.TranStat $ I.SAssume cond')
    -- exit loop transition
    ctxInsTrans aftbody after (I.TranStat $ I.SAssume $ I.EUnOp Not cond')

statToCFA' before after (SWhile _ _ cond stat) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    ctxLocSetAct loopback (I.ActExpr cond)
    ctxInsTrans loopback after (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    -- after condition has been checked, before the body
    befbody <- ctxInsTrans' loopback (I.TranStat $ I.SAssume cond')
    -- body
    ctxPushBrkLoc after
    aftbody <- statToCFA befbody stat
    -- loop-back transition
    ctxInsTrans aftbody loopback I.TranNop
    ctxPopBrkLoc

statToCFA' before after (SFor _ _ (minit, cond, inc) body) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    aftinit <- case minit of
                    Nothing -> return before
                    Just st -> statToCFA before st
    -- create target for loopback transition
    loopback <- ctxInsTrans' aftinit I.TranNop
    ctxLocSetAct loopback (I.ActExpr cond)
    ctxInsTrans loopback after (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    -- before loop body
    befbody <- ctxInsTrans' loopback $ I.TranStat $ I.SAssume cond'
    ctxPushBrkLoc after
    aftbody <- statToCFA befbody body
    -- after increment is performed at the end of loop iteration
    aftinc <- statToCFA aftbody inc
    ctxPopBrkLoc
    -- loopback transition
    ctxInsTrans aftinc loopback I.TranNop

statToCFA' before after (SChoice _ _ ss) = do
    v <- ctxInsTmpVar Nothing $ mkChoiceType $ length ss
    _ <- mapIdxM (\s i -> do aftAssume <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EVar (I.varName v) I.=== mkChoice v i)
                             aft <- statToCFA aftAssume s
                             ctxInsTrans aft after I.TranNop) ss
    return ()

statToCFA' before _ (SBreak _ _) = do
    brkLoc <- gets ctxBrkLoc
    ctxInsTrans before brkLoc I.TranNop

statToCFA' before after s@(SInvoke _ _ mref mas) = do
    sc <- gets ctxScope
    let meth = snd $ getMethod sc mref
    methInline before after meth mas Nothing (I.ActStat s)

statToCFA' before after (SAssert _ _ cond) | ?xducer  = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssert cond')

statToCFA' before after (SAssert _ _ cond) = do
    cond' <- exprToIExprDet cond
    when (cond' /= I.false) $ ctxInsTrans before after (I.TranStat $ I.SAssume cond')
    when (cond' /= I.true)  $ do aftcond <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
                                 ctxErrTrans aftcond after

statToCFA' before after (SAssume _ _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssume cond')

statToCFA' before after (SAssign _ _ lhs e@(EApply _ mref margs)) = do
    sc <- gets ctxScope
    let meth = snd $ getMethod sc mref
    methInline before after meth margs (Just lhs) (I.ActExpr e)

statToCFA' before after (SAssign _ _ lhs rhs) = do
    sc <- gets ctxScope
    let ?scope = sc
    let t = mkType $ exprType lhs
    lhs' <- exprToIExprDet lhs
    rhs' <- exprToIExprs rhs (exprTypeSpec lhs)
    ctxInsTransMany before after $ map I.TranStat
                                 $ zipWith I.SAssign (I.exprScalars lhs' t) 
                                                     (concatMap (uncurry I.exprScalars) rhs')

statToCFA' before after (SITE _ _ cond sthen mselse) = do
    cond' <- exprToIExpr cond (BoolSpec nopos)
    befthen <- ctxInsTrans' before (I.TranStat $ I.SAssume cond')
    aftthen <- statToCFA befthen sthen
    ctxInsTrans aftthen after I.TranNop
    befelse <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    aftelse <- case mselse of
                    Nothing    -> return befelse
                    Just selse -> statToCFA befelse selse
    ctxInsTrans aftelse after I.TranNop

statToCFA' before after (SCase _ _ e cs mdef) = do
    e'  <- exprToIExprDet e
    let (vs,ss) = unzip cs
    vs0 <- mapM exprToIExprDet vs
    let vs1 = map (\(c, prev) -> let cond = (I.EBinOp Eq e' c)
                                     dist = let ?pred = [] in
                                            map (I.EBinOp Neq c)
                                            $ filter ((\eq -> (not $ I.isConstExpr eq) || I.evalConstExpr eq == I.BoolVal True) . I.EBinOp Eq c)
                                            $ prev
                                 in I.conj (cond:dist))
                  $ zip vs0 (inits vs0)
    let negs = I.conj $ map (I.EBinOp Neq e') vs0
    let cs' = case mdef of
                   Nothing  -> (zip vs1 $ map Just ss) ++ [(negs, Nothing)]
                   Just def -> (zip vs1 $ map Just ss) ++ [(negs, Just def)]
    _ <- mapM (\(c,mst) -> do befst <- ctxInsTrans' before (I.TranStat $ I.SAssume c)
                              aftst <- case mst of 
                                            Nothing -> return befst
                                            Just st -> statToCFA befst st
                              ctxInsTrans aftst after I.TranNop) cs'
    return ()

statToCFA' before after s@(SMagic _ _) | ?nestedmb = do
    -- move action label to the pause location below
    ctxLocSetAct before I.ActNone
    -- don't wait for $magic in a nested magic block
    aftpause <- ctxPause before I.true (I.ActStat s) -- (I.ActStat $ atPos s p)
    -- debugger expects a nop-transition here
    ctxInsTrans aftpause after I.TranNop
                                       | otherwise = do
    ctxLocSetAct before I.ActNone
    -- magic block flag
    ---aftcheck <- ctxInsTrans' before $ I.TranStat $ I.SAssume $ mkMagicVar I.=== I.false
    aftmag <- ctxInsTrans' before $ I.TranStat $ mkMagicVar I.=: I.true
    -- wait for magic flag to be false
    aftwait <- ctxPause aftmag mkMagicDoneCond (I.ActStat s) --(I.ActStat $ atPos s p)
    ctxInsTrans aftwait after I.TranNop
--    where 
--    p = case constr of
--             Left  i -> pos i
--             Right c -> pos c

statToCFA' before after (SMagExit _ _) = 
    ctxInsTrans before after $ I.TranStat $ mkMagicVar I.=: I.false

statToCFA' before after (SDoNothing _ _) = 
    ctxInsTrans before after $ I.TranNop


methInline :: (?spec::Spec, ?procs::[I.Process], ?nestedmb::Bool, ?xducer::Bool) => I.Loc -> I.Loc -> Method -> [Maybe Expr] -> Maybe Expr -> I.LocAction -> State CFACtx ()
methInline before after meth margs mlhs act = do
    -- save current context
    mepid <- gets ctxEPID
    let mpid = case mepid of
                    Just (EPIDProc pid) -> Just pid
                    _                   -> Nothing
    let sc = ScopeMethod tmMain meth
    lhs <- case mlhs of
                Nothing  -> return Nothing
                Just lhs -> (liftM Just) $ exprToIExprDet lhs
    -- set input arguments
    aftarg <- setArgs before meth margs
    -- set return location
    retloc <- ctxInsLoc
    aftret <- ctxInsTrans' retloc I.TranReturn
    --ctxLocSetAct aftret act
    -- clear break location
    ctxPushBrkLoc $ error "break outside a loop"
    -- change syntactic scope
    ctxPushScope sc aftret lhs (methodLMap mpid meth)
    -- build CFA of the method
    aftcall <- ctxInsTrans' aftarg (I.TranCall meth aftret)
    aftbody <- statToCFA aftcall (fromRight $ methBody meth)
    ctxInsTrans aftbody retloc I.TranNop
    -- restore syntactic scope
    ctxPopScope
    -- copy out arguments
    aftout <- copyOutArgs aftret meth margs
    -- pause after task invocation
    aftpause <- if elem (methCat meth) [Task Controllable] && (mepid /= Just EPIDCont || ?nestedmb == True)
                   then ctxPause aftout I.true act
                   else do ctxLocSetAct aftout act
                           return aftout
    ctxInsTrans aftpause after I.TranNop
    -- restore context
    ctxPopBrkLoc

-- assign input arguments to a method
setArgs :: (?spec::Spec) => I.Loc -> Method -> [Maybe Expr] -> State CFACtx I.Loc 
setArgs before meth margs = do
    mepid  <- gets ctxEPID
    let nsid = maybe (NSID Nothing Nothing) (\epid -> epid2nsid epid (ScopeMethod tmMain meth)) mepid
    foldM (\bef (farg,Just aarg) -> do aarg' <- exprToIExprs aarg (tspec farg)
                                       let t = mkType $ Type (ScopeTemplate tmMain) (tspec farg)
                                       ctxInsTransMany' bef $ map I.TranStat
                                                            $ zipWith I.SAssign (I.exprScalars (mkVar nsid farg) t) 
                                                                                (concatMap (uncurry I.exprScalars) aarg'))
          before $ filter (\(a,_) -> argDir a == ArgIn) $ zip (methArg meth) margs

-- copy out arguments
copyOutArgs :: (?spec::Spec) => I.Loc -> Method -> [Maybe Expr] -> State CFACtx I.Loc
copyOutArgs loc meth margs = do
    mepid <- gets ctxEPID
    let nsid = maybe (NSID Nothing Nothing) (\epid -> epid2nsid epid (ScopeMethod tmMain meth)) mepid
    foldM (\loc' (farg,aarg) -> do aarg' <- exprToIExprDet aarg
                                   let t = mkType $ Type (ScopeTemplate tmMain) (tspec farg)
                                   ctxInsTransMany' loc' $ map I.TranStat
                                                         $ zipWith I.SAssign (I.exprScalars aarg' t) 
                                                                             (I.exprScalars (mkVar nsid farg) t)) loc
          $ map (mapSnd fromJust)
          $ filter (isJust . snd)
          $ filter ((== ArgOut) . argDir . fst) 
          $ zip (methArg meth) margs

------------------------------------------------------------------------------
-- Postprocessing
------------------------------------------------------------------------------

statAddNullTypes :: I.Spec -> I.Statement -> I.Statement
statAddNullTypes spec (I.SAssume (I.EBinOp Eq e (I.EConst (I.NullVal _)))) = let ?spec = spec in
                                                                             I.SAssume (I.EBinOp Eq e (I.EConst $ I.NullVal $ I.exprType e))
statAddNullTypes _    s = s

----------------------------------------------------------
-- Top-level function: convert process statement to CFA
----------------------------------------------------------

procStatToCFA :: (?spec::Spec, ?procs::[I.Process], ?nestedmb::Bool, ?xducer::Bool) => Statement -> I.Loc -> State CFACtx I.Loc
procStatToCFA stat before = do
    after <- statToCFA before stat
    ctxAddNullPtrTrans
    return after
