{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Frontend.StatementOps(mapStat,
                    mapStatM,
                    statMapExpr,
                    statMapTSpec,
                    statLabels,
                    statCallees,
                    statSubprocessRec,
                    statSubprocessNonrec,
                    statFlatten,
                    statObjs,
                    statObjsRec,
                    methObjsRec,
                    statReturns) where
import Prelude hiding ((<>))
import Control.Monad.Except
import Data.Maybe
import qualified Data.Traversable as Tr

import Util hiding (name, trace)
import Pos
import Name
import Frontend.Expr
import {-# SOURCE #-} Frontend.ExprOps
import Frontend.ExprFlatten
import Frontend.Spec
import Frontend.NS
import Frontend.Statement
import Frontend.Type
import Frontend.TypeOps
import Frontend.TVar
import Frontend.TVarOps
import Frontend.Method
import Frontend.Template
import Frontend.InstTree

-- Map function over all substatements
mapStat :: (?spec::Spec) => (Scope -> Statement -> Statement) -> Scope -> Statement -> Statement
mapStat f s (SSeq     p l ss)        = f s $ SSeq     p l (map (mapStat f s) ss)
mapStat f s (SPar     p l ss)        = f s $ SPar     p l (map (mapStat f s) ss)
mapStat f s (SForever p l b)         = f s $ SForever p l (mapStat f s b)
mapStat f s (SDo      p l b c)       = f s $ SDo      p l (mapStat f s b) c
mapStat f s (SWhile   p l c b)       = f s $ SWhile   p l c (mapStat f s b)
mapStat f s (SFor     p l (i,c,u) b) = f s $ SFor     p l ((fmap (mapStat f s) i),c, mapStat f s u) (mapStat f s b)
mapStat f s (SChoice  p l ss)        = f s $ SChoice  p l (map (mapStat f s) ss)
mapStat f s (SITE     p l c t me)    = f s $ SITE     p l c (mapStat f s t) (fmap (mapStat f s) me)
mapStat f s (SCase    p l c cs md)   = f s $ SCase    p l c (map (\(e,st) -> (e,mapStat f s st)) cs) (fmap (mapStat f s) md)
mapStat f s st                       = f s st

mapStatM :: (Monad m, ?spec::Spec) => (Scope -> Statement -> m Statement) -> Scope -> Statement -> m Statement
mapStatM f s (SSeq     p l ss)        = f s =<< (liftM  $ SSeq     p l)       (mapM (mapStatM f s) ss)
mapStatM f s (SPar     p l ss)        = f s =<< (liftM  $ SPar     p l)       (mapM (mapStatM f s) ss)
mapStatM f s (SForever p l b)         = f s =<< (liftM  $ SForever p l)       (mapStatM f s b)
mapStatM f s (SDo      p l b c)       = f s =<< (liftM  $ (flip $ SDo p l) c) (mapStatM f s b)
mapStatM f s (SWhile   p l c b)       = f s =<< (liftM  $ SWhile   p l c)     (mapStatM f s b)
mapStatM f s (SFor     p l (i,c,u) b) = do i' <- Tr.sequence $ fmap (mapStatM f s) i
                                           u' <- mapStatM f s u
                                           b' <- mapStatM f s b
                                           f s $ SFor p l (i', c, u') b'
mapStatM f s (SChoice  p l ss)        = f s =<< (liftM  $ SChoice  p l)       (mapM (mapStatM f s) ss)
mapStatM f s (SITE     p l c t me)    = f s =<< (liftM2 $ SITE     p l c)     (mapStatM f s t) (Tr.sequence $ fmap (mapStatM f s) me)
mapStatM f s (SCase    p l c cs md)   = do cs' <- mapM (\(e,st) -> do st' <- mapStatM f s st
                                                                      return (e,st')) cs
                                           md' <- Tr.sequence $ fmap (mapStatM f s) md
                                           f s $ SCase p l c cs' md'
mapStatM f s st                       = f s st


-- Map function over all TypeSpec's in the statement
statMapTSpec :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> Statement -> Statement
statMapTSpec f s st = mapStat (statMapTSpec' f) s st

statMapTSpec' :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> Statement -> Statement
statMapTSpec' f s (SVarDecl p l v) = SVarDecl p l (Var (pos v) (varMem v) (mapTSpec f s $ tspec v) (name v) (varInit v))
statMapTSpec' _ _ st               = st

-- Map function over all expressions in the statement
statMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Statement -> Statement
statMapExpr f s st = mapStat (statMapExpr' f) s st

statMapExpr' :: (?spec::Spec) =>  (Scope -> Expr -> Expr) -> Scope -> Statement -> Statement
statMapExpr' f s (SVarDecl p l v)            = SVarDecl p l (varMapExpr f s v)
statMapExpr' f s (SReturn  p l mr)           = SReturn  p l (fmap (mapExpr f s) mr)
statMapExpr' f s (SDo      p l b c)          = SDo      p l b (mapExpr f s c)
statMapExpr' f s (SWhile   p l c b)          = SWhile   p l (mapExpr f s c) b
statMapExpr' f s (SFor     p l (i,c,u) b)    = SFor     p l (i, mapExpr f s c, u) b
statMapExpr' f s (SInvoke  p l m mas)        = SInvoke  p l m (map (fmap $ mapExpr f s) mas)
statMapExpr' f s (SWait    p l e)            = SWait    p l (mapExpr f s e)
statMapExpr' f s (SAssert  p l e)            = SAssert  p l (mapExpr f s e)
statMapExpr' f s (SAssume  p l e)            = SAssume  p l (mapExpr f s e)
statMapExpr' f s (SAssign  p l lhs rhs)      = SAssign  p l (mapExpr f s lhs) (mapExpr f s rhs)
statMapExpr' f s (SITE     p l c t me)       = SITE     p l (mapExpr f s c) t me
statMapExpr' f s (SCase    p l c cs md)      = SCase    p l (mapExpr f s c) (map (mapFst $ mapExpr f s) cs) md
statMapExpr' _ _ (SMagic   p l)              = SMagic   p l
statMapExpr' _ _ st                          = st

-- Find all methods invoked by the statement
statCallees :: (?spec::Spec) => Scope -> Statement -> [(Pos, (Template, Method))]
statCallees s (SVarDecl _ _ v)            = fromMaybe [] $ fmap (exprCallees s) $ varInit v
statCallees s (SReturn  _ _ me)           = fromMaybe [] $ fmap (exprCallees s) me
statCallees s (SSeq     _ _ ss)           = concatMap (statCallees s) ss
statCallees s (SPar     _ _ ss)           = concatMap (statCallees s) ss
statCallees s (SForever _ _ b)            = statCallees s b
statCallees s (SDo      _ _ b c)          = statCallees s b ++ exprCallees s c
statCallees s (SWhile   _ _ c b)          = exprCallees s c ++ statCallees s b
statCallees s (SFor     _ _ (i,c,u) b)    = (fromMaybe [] $ fmap (statCallees s) i) ++ exprCallees s c ++ statCallees s u ++ statCallees s b
statCallees s (SChoice  _ _ ss)           = concatMap (statCallees s) ss
statCallees s (SInvoke  p _ mref mas)     = (p,getMethod s mref):(concatMap (exprCallees s) $ catMaybes mas)
statCallees s (SWait    _ _ e)            = exprCallees s e
statCallees s (SAssert  _ _ e)            = exprCallees s e
statCallees s (SAssume  _ _ e)            = exprCallees s e
statCallees s (SAssign  _ _ l r)          = exprCallees s l ++ exprCallees s r
statCallees s (SITE     _ _ c t me)       = exprCallees s c ++ statCallees s t ++ (fromMaybe [] $ fmap (statCallees s) me)
statCallees s (SCase    _ _ c cs md)      = exprCallees s c ++ 
                                            concatMap (\(e,st) -> exprCallees s e ++ statCallees s st) cs ++
                                            (fromMaybe [] $ fmap (statCallees s) md)
statCallees _ _                           = []


-- Objects referred to by the statement
statObjs :: (?spec::Spec, ?scope::Scope) => Statement -> [Obj]
statObjs (SVarDecl _ _ v)             = (ObjVar ?scope v) : (concatMap exprObjs $ maybeToList $ varInit v)
statObjs (SReturn  _ _ mr)            = concatMap exprObjs $ maybeToList mr
statObjs (SSeq     _ _ ss)            = concatMap statObjs ss
statObjs (SPar     _ _ ps)            = concatMap statObjs ps
statObjs (SForever _ _ s)             = statObjs s
statObjs (SDo      _ _ s c)           = statObjs s ++ exprObjs c
statObjs (SWhile   _ _ c s)           = statObjs s ++ exprObjs c
statObjs (SFor     _ _ (mi, c, i) s)  = statObjs s ++ exprObjs c ++ statObjs i ++ (concatMap statObjs $ maybeToList mi)
statObjs (SChoice  _ _ ss)            = concatMap statObjs ss
statObjs (SInvoke  _ _ m mas)         = (let (t,meth) = getMethod ?scope m in ObjMethod t meth):
                                        (concatMap exprObjs $ catMaybes mas)
statObjs (SWait    _ _ c)             = exprObjs c
statObjs (SAssert  _ _ c)             = exprObjs c
statObjs (SAssume  _ _ c)             = exprObjs c
statObjs (SAssign  _ _ l r)           = exprObjs l ++ exprObjs r
statObjs (SITE     _ _ c t me)        = exprObjs c ++ statObjs t ++ (concatMap statObjs $ maybeToList me)
statObjs (SCase    _ _ c cs md)       = exprObjs c ++
                                        concatMap (\(e,s) -> exprObjs e ++ statObjs s) cs ++
                                        concatMap statObjs (maybeToList md)
statObjs _                            = []

-- recursive version
statObjsRec :: (?spec::Spec, ?scope::Scope) => Statement -> [Obj]
statObjsRec s =
    let os = statObjs s
        mos = filter (\o -> case o of
                                 ObjMethod _ _ -> True
                                 _             -> False) os
        os' = concatMap (\(ObjMethod t m) -> methObjsRec t m) mos
    in os ++ os'

-- Recursively compute objects referenced in the body of the method
methObjsRec :: (?spec::Spec) => Template -> Method -> [Obj]
methObjsRec t m = 
    let ?scope = ScopeMethod t m
    in case methBody m of
            Left (ms1,ms2) -> concatMap statObjsRec $ maybeToList ms1 ++ maybeToList ms2
            Right s        -> statObjsRec s

-- List of subprocesses spawned by the statement:
-- Computed by recursing through fork statements
statSubprocessRec :: (?spec::Spec) => Statement -> [Statement]
statSubprocessRec (SSeq     _ _ ss)         = concatMap statSubprocessRec ss
statSubprocessRec (SPar     _ _ ss)         = ss ++ concatMap statSubprocessRec ss
statSubprocessRec (SForever _ _ b)          = statSubprocessRec b
statSubprocessRec (SDo      _ _ b _)        = statSubprocessRec b
statSubprocessRec (SWhile   _ _ _ b)        = statSubprocessRec b
statSubprocessRec (SFor     _ _ (mi,_,s) b) = concatMap statSubprocessRec $ (maybeToList mi) ++ [s,b]
statSubprocessRec (SChoice  _ _ ss)         = concatMap statSubprocessRec ss
statSubprocessRec (SITE     _ _ _ t me)     = concatMap statSubprocessRec $ t:(maybeToList me)
statSubprocessRec (SCase    _ _ _ cs mdef)  = concatMap statSubprocessRec $ map snd cs ++ maybeToList mdef
statSubprocessRec _                         = []

-- non-recursive (first-level subprocesses only)
statSubprocessNonrec :: (?spec::Spec) => Statement -> [Statement]
statSubprocessNonrec (SSeq     _ _ ss)         = concatMap statSubprocessNonrec ss
statSubprocessNonrec (SPar     _ _ ss)         = ss 
statSubprocessNonrec (SForever _ _ b)          = statSubprocessNonrec b
statSubprocessNonrec (SDo      _ _ b _)        = statSubprocessNonrec b
statSubprocessNonrec (SWhile   _ _ _ b)        = statSubprocessNonrec b
statSubprocessNonrec (SFor     _ _ (mi,_,s) b) = concatMap statSubprocessNonrec $ (maybeToList mi) ++ [s,b]
statSubprocessNonrec (SChoice  _ _ ss)         = concatMap statSubprocessNonrec ss
statSubprocessNonrec (SITE     _ _ _ t me)     = concatMap statSubprocessNonrec $ t:(maybeToList me)
statSubprocessNonrec (SCase    _ _ _ cs mdef)  = concatMap statSubprocessNonrec $ map snd cs ++ maybeToList mdef
statSubprocessNonrec _                         = []


statFlatten :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten iid s st = mapStat (statFlatten' iid) s $ statMapExpr (exprFlatten' iid) s st

statFlatten' :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten' iid s st = statFlatten'' iid s $ st{stLab = fmap (\l -> itreeFlattenName iid l) $ stLab st}

statFlatten'' :: (?spec::Spec) => IID -> Scope -> Statement -> Statement
statFlatten'' iid _ (SInvoke p l (MethodRef p' n) as) = SInvoke p l (MethodRef p' [itreeFlattenName (itreeRelToAbsPath iid (init n)) (last n)]) as
statFlatten'' _   _ st                                = st

-- True if the statement returns a value on all execution paths.
statReturns :: Statement -> Bool
statReturns (SReturn  _ _ r)             = isJust r
statReturns (SSeq     _ _ ss)            = statReturns $ last ss
statReturns (SChoice  _ _  ss)           = all statReturns ss
statReturns (SITE     _ _ _ t (Just e))  = statReturns t && statReturns e
statReturns (SCase    _ _ _ cs (Just d)) = all statReturns (d: (map snd cs))
statReturns _                            = False

statLabels :: Statement -> [Ident]
statLabels s = (maybeToList $ stLab s) ++ statLabels' s

statLabels' :: Statement -> [Ident]
statLabels' (SSeq _ _ ss)         = concatMap statLabels ss
statLabels' (SPar _ _ ss)         = concatMap statLabels ss
statLabels' (SForever _ _ s)      = statLabels s
statLabels' (SDo _ _ b _)         = statLabels b
statLabels' (SWhile _ _ _ b)      = statLabels b
statLabels' (SFor _ _ (mi,_,s) b) = concatMap statLabels $ b:s:(maybeToList mi)
statLabels' (SChoice _ _ ss)      = concatMap statLabels ss
statLabels' (SITE _ _ _ t e)      = statLabels t ++ maybe [] statLabels e
statLabels' (SCase _ _ _ cs md)   = concatMap statLabels $ (map snd cs) ++ maybeToList md
statLabels' _                     = []
