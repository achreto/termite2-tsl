{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Frontend.StatementValidate(validateStat,
                                  validateStat') where

import Control.Monad.Except
import Data.Maybe
import Data.List

import TSLUtil
import Util hiding (name, trace)
import Pos
import Frontend.Expr
import Frontend.ExprOps
import Frontend.ExprValidate
import Frontend.Spec
import Frontend.NS
import Frontend.Statement
import Frontend.TypeOps
import Frontend.Type
import Frontend.TVarValidate
import Frontend.Method

-------------------------------------------------------------------------
-- Validation
-------------------------------------------------------------------------

validateStat :: (?spec::Spec, ?privoverride::Bool, MonadError String me) => Scope -> Statement -> me ()
validateStat s st = do let ?scope = s 
                       validateStat' False st

-- The first argument indicates that the statement belongs to a loop
validateStat' :: (?spec::Spec, ?privoverride::Bool, ?scope::Scope, MonadError String me) => Bool -> Statement -> me ()
validateStat' _ (SVarDecl p _ v) = do 
    assert (not $ isTemplateScope ?scope) p "variable declaration inside always-block"
    validateVar ?scope v
    validateVar2 ?scope v

validateStat' _ (SReturn p _ me) = do
    case ?scope of
         ScopeMethod  _ m  -> case methRettyp m of
                                   Nothing -> assert (isNothing me) p "cannot return value from method with void return type"
                                   Just t  -> do assert (isJust me) p "return value not specified"
                                                 validateExpr' (fromJust me)
                                                 checkTypeMatch (fromJust me) (Type ?scope t) (exprType $ fromJust me)
         ScopeProcess _ pr -> assert (isNothing me) p "cannot return value from a process"
         ScopeTransducer _ -> err p "return statement inside transducer"
         ScopeTemplate _   -> err p "return statement inside always-block"

validateStat' l (SSeq _ _ ss) = do
    mapM (validateStat' l) ss
    return ()

validateStat' l (SPar p _ ss) = do
    mapM (\s -> assert (isJust $ stLab s) (pos s) "unlabelled forked process") ss
    mapM (validateStat' l) ss
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "fork inside function"
                                  Procedure         -> err p "fork inside procedure"
                                  Task Controllable -> err p "fork inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ pr -> return ()
         ScopeTemplate _   -> err p $ "fork inside always-block"
         ScopeTransducer _ -> err p $ "fork inside transducer"

validateStat' _ (SForever _ _ b) = do
    checkLoopBody b

validateStat' _ (SDo _ _ b c) = do
    validateRegExpr' c
    assert (isBool $ exprType c) (pos c) "loop condition is not of boolean type"
    checkLoopBody b

validateStat' _ (SWhile _ _ c b) = do
    validateRegExpr' c
    assert (isBool $ exprType c) (pos c) "loop condition is not of boolean type"
    checkLoopBody b

validateStat' _ (SFor _ _ (mi, c, s) b) = do
    validateRegExpr' c
    assert (isBool $ exprType c) (pos c) "loop condition is not of boolean type"
    case mi of
         Just i  -> validateStat' False i
         Nothing -> return ()
    validateStat' False s
    checkLoopBody b

validateStat' l (SChoice p _ ss) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function            -> err p "non-deterministic choice inside function"
                                  Procedure           -> err p "non-deterministic choice inside procedure"
                                  Task Uncontrollable -> err p "non-deterministic choice inside uncontrollable task"
                                  _                   -> return ()
         ScopeProcess _ _  -> return ()
         ScopeTemplate _   -> err p "non-deterministic choice inside always-block"
         ScopeTransducer _ -> return ()
    mapM (validateStat' l) ss
    return ()

validateStat' _ (SPause p _) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "pause inside function"
                                  Procedure         -> err p "pause inside procedure"
                                  Task Controllable -> err p "pause inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ _  -> return ()
         ScopeTemplate _   -> err p "pause inside always-block"
         ScopeTransducer _ -> return ()

validateStat' _ (SStop p _) = do
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "stop inside function"
                                  Procedure         -> err p "stop inside procedure"
                                  Task Controllable -> err p "stop inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ _  -> return ()
         ScopeTemplate _   -> err p "stop inside always-block"
         ScopeTransducer _ -> err p "stop inside transducer"

validateStat' _ (SWait p _ e) = do
    validateExpr' e
    assert (isBool $ exprType e) (pos e) "wait condition is not of boolean type"
    -- because we do not handle them correctly during inlining
    assert (null $ exprCallees ?scope e) (pos e) $ "Method invocations not allowed inside wait conditions"
    assert (not $ any (\o -> case o of
                                  ObjWire _ _ -> True
                                  _           -> False) $ exprObjs e) (pos e) $ "Wires not allowed inside wait conditions"
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function          -> err p "wait inside function"
                                  Procedure         -> err p "wait inside procedure"
                                  Task Controllable -> err p "wait inside controllable task"
                                  _                 -> return ()
         ScopeProcess _ _  -> return ()
         ScopeTemplate _   -> err p "wait inside always-block"
         ScopeTransducer _ -> err p "wait inside transducer"

validateStat' l (SBreak p _) = assert l p "break outside a loop"
validateStat' _ (SInvoke p _ m as) = validateCall p m as
validateStat' _ (SAssert _ _ e) = do
    validateRegExpr' e
    assert (isBool $ exprType e) (pos e) "Assertion must be a boolean expression"
    assert (exprNoSideEffects e) (pos e) "Assertion must be side-effect free"
    assert (not $ isFunctionScope ?scope) (pos e) "Assertions not allowed inside functions"
    assert (not $ isTemplateScope ?scope) (pos e) "Assertions not allowed inside always-blocks"

validateStat' _ (SAssume _ _ e) = do
    validateRegExpr' e
    assert (isBool $ exprType e) (pos e) "Assumption must be a boolean expression"
    assert (exprNoSideEffects e) (pos e) "Assumption must be side-effect free"

validateStat' _ (SAssign _ _ lhs rhs) = do
    validateExpr' lhs
    validateRegExpr' rhs
    assert (isLExpr lhs) (pos lhs)   $ "Left-hand side of assignment is not an L-value"
    assert (not $ isSeqContainer $ exprType lhs) (pos lhs) $ "Left-hand side of assignment (or one of its members) is a sequence"
    checkTypeMatch rhs (exprType lhs) (exprType rhs)
    -- No modifications to global variables in a function
    if isFunctionScope ?scope 
       then assert (isLocalLHS lhs) (pos lhs) "Global state modification inside a function"
       else return ()

validateStat' l (SITE _ _ i t e) = do
    validateRegExpr' i
    checkTypeMatch i (Type ?scope $ BoolSpec nopos) (exprType i)
    validateStat' l t
    case e of 
         Just s  -> validateStat' l s
         Nothing -> return ()

validateStat' l (SCase p _ c cs md) = do
    validateRegExpr' c
    assert (length cs > 0) p "Empty case statement"
    mapM (\(e,s) -> do validateRegExpr' e
                       validateStat' l s
                       assert (exprNoSideEffects e) (pos e) "Case label must be side-effect free") cs
    case md of
         Just d  -> validateStat' l d
         Nothing -> return ()
    mapM_ (\(e1,_) -> checkTypeMatch e1 (exprType c) (exprType e1)) cs

validateStat' _ (SIn _ _ l r) = do
    validateRegExpr' l
    validateExpr' r
    assert (isLExpr l) (pos l) $ show l ++ " is not an L-value"
    assert (isSequence $ exprType r) (pos r) $ "Not a sequence expression " ++ show r
    assert (isXInputExpr r) (pos r) $ "Right-hand side of << must refer to an input port"

validateStat' _ (SOut _ _ l r) = do
    validateRegExpr' l
    validateExpr' r
    assert (isSequence $ exprType r) (pos r) $ "Not a sequence expression " ++ show r
    assert (isXOutputExpr r) (pos r) $ "Right-hand side of >> must refer to an output port"

validateStat' l (SMagic p _) = do
    case ?scope of
         ScopeMethod t m -> assert (methCat m == Task Uncontrollable) p "Magic blocks only allowed in uncontrollable tasks"
         _               -> err p "Magic blocks only allowed in uncontrollable tasks"

-- There is no path through the loop body that does not break out of the loop and
-- does not contain some form of pause
checkLoopBody :: (?spec::Spec, ?scope::Scope, ?privoverride::Bool, MonadError String me) => Statement -> me ()
checkLoopBody s = do
    validateStat' True s
    case findInstPath False s of
         Nothing -> return ()
         Just p  -> err (pos s) $ "Instanteneous path exists through the body of the loop:" ++
                                  (concat $ map (\s -> "\n    " ++ case s of 
                                                                        Left st -> spos st ++ ": " ++ show st
                                                                        Right e -> spos e  ++ ": " ++ show e) p)
                                  
-- Find instantaneous path through the statement.  
-- If the first argument is true, then Break is considered
-- instantaneous; otherwise it's not.
findInstPath :: (?spec::Spec, ?scope::Scope) => Bool -> Statement -> Maybe [Either Statement Expr]
findInstPath _     s@(SVarDecl _ _ _)    = Just []
findInstPath _       (SReturn _ _ _)     = Nothing
findInstPath b     s@(SSeq _ _ ss)       = let ps  = map (findInstPath b) ss
                                               ps' = case findIndex (\p -> isJust p && 
                                                                           (not $ null $ fromJust p) && 
                                                                           isBreak (last $ fromJust p)) ps of
                                                          Nothing -> ps
                                                          Just i  -> take (i+1) ps
                                           in if all isJust ps'
                                                 then Just $ concat $ map fromJust ps'
                                                 else Nothing
findInstPath _       (SPar _ _ _)        = Nothing
findInstPath _       (SForever _ _ s)    = findInstPath True s
findInstPath _       (SDo _ _ s _)       = findInstPath True s -- a do-loop performs at least one iteration
findInstPath _     s@(SWhile _ _ c _)    = if isInstExpr c then Just [Right c] else Nothing -- while and for-loops can terminate instantaneously
findInstPath _     s@(SFor _ _ _ _)      = Just [Left s]
findInstPath b       (SChoice _ _ ss)    = shortest $ catMaybes $ map (findInstPath b) ss
findInstPath _       (SPause _ _)        = Nothing
findInstPath _       (SWait _ _ _)       = Nothing
findInstPath _       (SStop _ _)         = Nothing
findInstPath True  s@(SBreak _ _)        = Just [Left s]
findInstPath False s@(SBreak _ _)        = Nothing
findInstPath b     s@(SInvoke _ _ m mas) = let (_,meth) = getMethod ?scope m
                                           in if elem (methCat meth) [Function,Procedure,Task Uncontrollable,Task Invisible] 
                                                 then if all isInstExpr $ catMaybes mas 
                                                         then Just [Left s]
                                                         else Nothing
                                                 else Nothing
findInstPath _     s@(SAssert _ _ _)     = Just [Left s]
findInstPath _     s@(SAssume _ _ _)     = Just [Left s]
findInstPath _     s@(SAssign _ _ _ r)   = if isInstExpr r then Just [Left s] else Nothing
findInstPath b     s@(SITE _ _ c t e)    = if not $ isInstExpr c 
                                              then Nothing
                                              else case e of 
                                                        Nothing -> Just [Right c]
                                                        Just st -> shortest $ catMaybes $ map (findInstPath b) $ [t,st]
findInstPath b     s@(SCase _ _ _ cs md) = shortest $ catMaybes $ map (findInstPath b) $ (map snd cs) ++ maybeToList md
findInstPath _       (SMagic _ _)        = Nothing
findInstPath _       (SIn _ _ _ _)       = Nothing
findInstPath _     s@(SOut _ _ _ _)      = Just [Left s]


isBreak :: Either Statement Expr -> Bool
isBreak (Left (SBreak _ _)) = True
isBreak _                 = False

-- Return a path that ends with a break if one exists;
-- otherwise return the first path from the list of Nothing
-- if the list is empty
shortest :: [[Either Statement Expr]] -> Maybe [Either Statement Expr]
shortest [] = Nothing
shortest ps = case find (\p -> if' (null p) False (isBreak $ last p)) ps of
                   Nothing -> Just $ head ps
                   Just p  -> Just p
