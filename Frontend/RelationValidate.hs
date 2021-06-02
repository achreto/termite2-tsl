{-# LANGUAGE RecordWildCards, ImplicitParams, FlexibleContexts #-}

module Frontend.RelationValidate(validateRelation,
                        validateApply) where

import Control.Monad.Except

import TSLUtil
import Pos
import Frontend.Relation
import Frontend.Template
import Frontend.Spec
import Name
import Frontend.Type
import Frontend.NS
import Frontend.TypeValidate
import Frontend.ExprValidate
import Frontend.ExprInline
import Frontend.ExprOps
import Frontend.TypeOps

validateRelation :: (?spec::Spec, MonadError String me) => Template -> Relation -> me ()
validateRelation tm r@Relation{..} = do 
    -- argument names are unique
    uniqNames (\n -> "Argument " ++ n ++ " declared multiple times in relation " ++ sname r) relArg
    let ?privoverride = False
    -- validate argument types
    _ <- mapM (\a -> case tspec a of
                          StructSpec _ _ -> err (pos $ tspec a) "Inline struct declaration is illegal in relation argument" -- because then there is no way to pass such an argument by value
                          _              -> return ())
              relArg
    _ <- mapM (\a -> do validateTypeSpec (ScopeTemplate tm)  $ tspec a
                        validateTypeSpec2 (ScopeTemplate tm) $ tspec a) relArg
    -- validate rule expressions
    _ <- mapM (validateExpr (ScopeRelation tm r) . ruleExpr) relRule
    _ <- mapM (\Rule{..} -> do let ?scope = ScopeRelation tm r 
                               assert (isBool $ exprType ruleExpr) (pos ruleExpr) "Relation interpretation must be a boolean expression"
                               assert (exprNoSideEffects ruleExpr) (pos ruleExpr) "Relation interpretation must be a side-effect-free expression"
                               assert (isPureExpr ruleExpr)        (pos ruleExpr) "Relation interpretation must be a pure expression"
                               assert (exprIsSimple ruleExpr)      (pos ruleExpr) "Rule expression too complex" -- makes sure we do not need to constuct a CFA when inlining rule expression
                               return ()) relRule
    return ()
