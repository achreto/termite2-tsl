{-# LANGUAGE ImplicitParams, TupleSections #-}

module StatementInline(statSimplify, 
                       procStatToCFA) where

import Control.Monad
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.Traversable as Tr

import Util hiding (name,trace)
import Inline
import TSLUtil
import Spec
import Pos
import Name
import NS
import Statement
import Expr
import TVar
import Method
import Type
import TypeOps
import ExprOps
import ExprInline
import PID

import qualified IExpr as I
import qualified CFA   as I
import qualified IVar  as I
import qualified ISpec as I

statSimplify :: (?spec::Spec, ?scope::Scope) => Statement -> NameGen Statement
statSimplify s = (liftM $ sSeq (pos s)) $ statSimplify' s

statSimplify' :: (?spec::Spec, ?scope::Scope) => Statement -> NameGen [Statement]
statSimplify' s@(SVarDecl p v) = 
    case varInit v of
         Just e  -> do asn <- statSimplify' $ SAssign p (ETerm (pos $ varName v) [varName v]) e
                       return $ s {-SVarDecl p v{varInit = Nothing}-} : asn
         Nothing -> return [s]

statSimplify' (SReturn p (Just e)) = do
    (ss,e') <- exprSimplify e
    return $ ss ++ [SReturn p (Just e')]

statSimplify' (SSeq p ss)           = (liftM $ return . SSeq p . concat) $ mapM statSimplify' ss
statSimplify' (SPar p ss)           = (liftM $ return . SPar p)          $ mapM (\(n,s) -> liftM (n,) $ statSimplify s) ss
statSimplify' (SForever p s)        = (liftM $ return . SForever p)      $ statSimplify s
statSimplify' (SDo p b c)           = do (ss,c') <- exprSimplify c
                                         b'      <- statSimplify' b
                                         return [SDo p (sSeq (pos b) (b'++ss)) c']
statSimplify' (SWhile p c b)        = do (ss,c') <- exprSimplify c
                                         b'      <- statSimplify' b
                                         return $ ss ++ [SWhile p c' (sSeq (pos b) (b'++ss))]
statSimplify' (SFor p (mi, c, s) b) = do i' <- case mi of
                                                    Nothing -> return []
                                                    Just i  -> statSimplify' i
                                         (ss,c') <- exprSimplify c
                                         s' <- statSimplify s
                                         b' <- statSimplify' b
                                         return $ i' ++ ss ++ [SFor p (Nothing, c',s') (sSeq (pos b) (b'++ss))]
statSimplify' (SChoice p ss)        = liftM (return . SChoice p)         $ mapM statSimplify ss
statSimplify' (SInvoke p mref mas)  = -- Order of argument evaluation is undefined in C;
                                      -- Go left-to-right
                                      do (ss, as') <- liftM unzip $ mapM (maybe (return ([], Nothing)) ((liftM $ mapSnd Just) . exprSimplify)) mas
                                         return $ (concat ss) ++ [SInvoke p mref as']
statSimplify' (SWait p c)           = do (ss,c') <- exprSimplify c
                                         return $ case ss of
                                                       [] -> [SWait p c']
                                                       _  -> (SPause p) : (ss ++ [SAssume p c'])
statSimplify' (SAssert p c)         = do (ss,c') <- exprSimplify c
                                         return $ ss ++ [SAssert p c']
statSimplify' (SAssume p c)         = do (ss,c') <- exprSimplify c
                                         return $ ss ++ [SAssume p c']
statSimplify' (SAssign p l r)       = -- Evaluate lhs first
                                      do (ssl,l') <- exprSimplify l
                                         ssr <- exprSimplifyAsn p l' r
                                         return $ ssl ++ ssr
statSimplify' (SITE p c t me)       = do (ss,c') <- exprSimplify c
                                         t'      <- statSimplify t
                                         me'     <- Tr.sequence $ fmap statSimplify me
                                         return $ ss ++ [SITE p c' t' me']
statSimplify' (SCase p c cs md)     = -- Case labels must be side-effect-free, so it is ok to 
                                      -- evaluate them in advance
                                      do (ssc,c')      <- exprSimplify c
                                         (sscs,clabs') <- (liftM unzip) $ mapM exprSimplify (fst $ unzip cs)
                                         cstats        <- mapM statSimplify (snd $ unzip cs)
                                         md'           <- Tr.sequence $ fmap statSimplify md
                                         return $ concat sscs ++ ssc ++ [SCase p c' (zip clabs' cstats) md']
statSimplify' (SMagic p p2 (Right e)) = do (ss,e') <- exprSimplify e
                                           return $ (SMagic p p2 (Right $ EBool (pos e) True)):(ss ++ [SAssert (pos e) e'])
statSimplify' st                      = return [st]



----------------------------------------------------------
-- Convert statement to CFA
----------------------------------------------------------
statToCFA :: (?spec::Spec, ?procs::[I.Process]) => I.Loc -> Statement -> State CFACtx I.Loc
statToCFA before   (SSeq _ ss)    = foldM statToCFA before ss
statToCFA before s@(SPause _)     = do ctxLocSetAct before (I.ActStat s)
                                       ctxPause before I.true (I.ActStat s)
statToCFA before s@(SWait _ c)    = do ctxLocSetAct before (I.ActStat s)
                                       ci <- exprToIExprDet c
                                       ctxPause before ci (I.ActStat s)
statToCFA before s@(SStop _)      = do ctxLocSetAct before (I.ActStat s)
                                       ctxFinal before
statToCFA before   (SVarDecl _ v) | isJust (varInit v) = return before
statToCFA before   (SVarDecl _ v) | otherwise = do 
                                       sc <- gets ctxScope
                                       let ?scope = sc
                                       let scalars = exprScalars $ ETerm nopos [name v]
                                       foldM (\loc e -> do e' <- exprToIExprDet e
                                                           let val = case tspec $ typ' e of
                                                                          BoolSpec _    -> I.BoolVal False
                                                                          UIntSpec _ w  -> I.UIntVal w 0
                                                                          SIntSpec _ w  -> I.SIntVal w 0
                                                                          EnumSpec _ es -> I.EnumVal $ sname $ head es
                                                                          PtrSpec  _ t  -> I.NullVal $ mkType $ Type sc t
                                                           ctxInsTrans' loc $ I.TranStat $ e' I.=: I.EConst val)
                                             before scalars
statToCFA before s@stat           = do ctxLocSetAct before (I.ActStat s)
                                       after <- ctxInsLoc
                                       statToCFA' before after stat
                                       return after

-- Only safe to call from statToCFA.  Do not call this function directly!
statToCFA' :: (?spec::Spec, ?procs::[I.Process]) => I.Loc -> I.Loc -> Statement -> State CFACtx ()
statToCFA' before _ (SReturn _ rval) = do
    -- add transition before before to return location
    mlhs  <- gets ctxLHS
    ret   <- gets ctxRetLoc
    case rval of 
         Nothing -> ctxInsTrans before ret I.TranReturn
         Just v  -> case mlhs of
                         Nothing  -> ctxInsTrans before ret I.TranNop
                         Just lhs -> do sc@(ScopeMethod _ m) <- gets ctxScope
                                        let t = fromJust $ methRettyp m
                                        vi <- exprToIExprs v t
                                        let asns = map I.TranStat
                                                   $ zipWith I.SAssign (I.exprScalars lhs (mkType $ Type sc t))
                                                                       (concatMap (uncurry I.exprScalars) vi)
                                        aftargs <- ctxInsTransMany' before asns
                                        ctxInsTrans aftargs ret I.TranReturn

statToCFA' before after s@(SPar _ ps) = do
    Just (EPIDProc pid) <- gets ctxEPID
    -- child process pids
    let pids  = map (childPID pid . sname . fst) ps
    -- enable child processes
    aften <- ctxInsTransMany' before $ map (\pid' -> I.TranStat $ mkEnVar pid' Nothing I.=: I.true) pids
    let mkFinalCheck (n,_) = I.disj $ map (\loc -> mkPCEq pcfa pid' (mkPC pid' loc)) $ I.cfaFinal pcfa
                             where pid' = childPID pid $ sname n
                                   p = fromJustMsg ("mkFinalCheck: process " ++ show pid' ++ " unknown") 
                                       $ find ((== sname n) . I.procName) ?procs
                                   pcfa = I.procCFA p
    -- pause and wait for all of them to reach final states
    aftwait <- ctxPause aften (I.conj $ map mkFinalCheck ps) (I.ActStat s)
    -- Disable forked processes and bring them back to initial states
    aftreset <- ctxInsTransMany' aftwait $ map (\(n,_) -> let pid' = childPID pid $ sname n
                                                              pcfa = I.procCFA $ fromJust $ find ((== sname n) . I.procName) ?procs
                                                          in mkPCAsn pcfa pid' (mkPC pid' I.cfaInitLoc)) ps
    aftdisable <- ctxInsTransMany' aftreset $ map  (\pid' -> I.TranStat $ mkEnVar pid' Nothing I.=: I.false) pids
    ctxInsTrans aftdisable after I.TranNop

statToCFA' before after (SForever _ stat) = do
    ctxPushBrkLoc after
    -- create target for loopback transition
    loopback <- ctxInsTrans' before I.TranNop
    -- loc' = end of loop body
    loc' <- statToCFA loopback stat
    -- loop-back transition
    ctxInsTrans loc' loopback I.TranNop
    ctxPopBrkLoc

statToCFA' before after (SDo _ stat cond) = do
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

statToCFA' before after (SWhile _ cond stat) = do
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

statToCFA' before after (SFor _ (minit, cond, inc) body) = do
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

statToCFA' before after (SChoice _ ss) = do
    v <- ctxInsTmpVar $ mkChoiceType $ length ss
    _ <- mapIdxM (\s i -> do aftAssume <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EVar (I.varName v) I.=== mkChoice v i)
                             aft <- statToCFA aftAssume s
                             ctxInsTrans aft after I.TranNop) ss
    return ()

statToCFA' before _ (SBreak _) = do
    brkLoc <- gets ctxBrkLoc
    ctxInsTrans before brkLoc I.TranNop

statToCFA' before after s@(SInvoke _ mref mas) = do
    sc <- gets ctxScope
    let meth = snd $ getMethod sc mref
    methInline before after meth mas Nothing (I.ActStat s)

statToCFA' before after (SAssert _ cond) = do
    cond' <- exprToIExprDet cond
    when (cond' /= I.false) $ ctxInsTrans before after (I.TranStat $ I.SAssume cond')
    when (cond' /= I.true)  $ do aftcond <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
                                 ctxErrTrans aftcond after

statToCFA' before after (SAssume _ cond) = do
    cond' <- exprToIExprDet cond
    ctxInsTrans before after (I.TranStat $ I.SAssume cond')

statToCFA' before after (SAssign _ lhs e@(EApply _ mref margs)) = do
    sc <- gets ctxScope
    let meth = snd $ getMethod sc mref
    methInline before after meth margs (Just lhs) (I.ActExpr e)

statToCFA' before after (SAssign _ lhs rhs) = do
    sc <- gets ctxScope
    let ?scope = sc
    let t = mkType $ typ lhs
    lhs' <- exprToIExprDet lhs
    rhs' <- exprToIExprs rhs (tspec lhs)
    ctxInsTransMany before after $ map I.TranStat
                                 $ zipWith I.SAssign (I.exprScalars lhs' t) 
                                                     (concatMap (uncurry I.exprScalars) rhs')

statToCFA' before after (SITE _ cond sthen mselse) = do
    cond' <- exprToIExprDet cond
    befthen <- ctxInsTrans' before (I.TranStat $ I.SAssume cond')
    aftthen <- statToCFA befthen sthen
    ctxInsTrans aftthen after I.TranNop
    befelse <- ctxInsTrans' before (I.TranStat $ I.SAssume $ I.EUnOp Not cond')
    aftelse <- case mselse of
                    Nothing    -> return befelse
                    Just selse -> statToCFA befelse selse
    ctxInsTrans aftelse after I.TranNop

statToCFA' before after (SCase _ e cs mdef) = do
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

statToCFA' before after s@(SMagic _ _ constr) = do
    -- magic block flag
    -- if this check is to be re-introduced, it should 
    ---aftcheck <- ctxInsTrans' before $ I.TranStat $ I.SAssume $ mkMagicVar I.=== I.false
    aftmag <- ctxInsTrans' before $ I.TranStat $ mkMagicVar I.=: I.true
    -- wait for magic flag to be false
    let p = case constr of
                 Left  i -> pos i
                 Right c -> pos c
    aftwait <- ctxPause aftmag mkMagicDoneCond (I.ActStat $ atPos s p)
    ctxInsTrans aftwait after I.TranNop

statToCFA' before after (SMagExit _) = do
--    aftcont <- ctxInsTrans' before  $ I.TranStat $ mkContVar  I.=: I.false
--    aftpid  <- ctxInsTrans' aftcont $ I.TranStat $ mkPIDVar   I.=: mkPIDEnum pidCont
    ctxInsTrans before after $ I.TranStat $ mkMagicVar I.=: I.false

methInline :: (?spec::Spec,?procs::[I.Process]) => I.Loc -> I.Loc -> Method -> [Maybe Expr] -> Maybe Expr -> I.LocAction -> State CFACtx ()
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
    aftcall <- ctxInsTrans' aftarg (I.TranCall meth (Just aftret))
    aftbody <- statToCFA aftcall (fromRight $ methBody meth)
    ctxInsTrans aftbody retloc I.TranNop
    -- restore syntactic scope
    ctxPopScope
    -- copy out arguments
    aftout <- copyOutArgs aftret meth margs
    -- pause after task invocation
    aftpause <- if elem (methCat meth) [Task Controllable] && (mepid /= Just EPIDCont)
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

----------------------------------------------------------
-- Top-level function: convert process statement to CFA
----------------------------------------------------------

procStatToCFA :: (?spec::Spec, ?procs::[I.Process]) => Statement -> I.Loc -> State CFACtx I.Loc
procStatToCFA stat before = do
    after <- statToCFA before stat
    ctxAddNullPtrTrans
    return after
