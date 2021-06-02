{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.TVarOps(varMapExpr, varType) where

import Control.Monad.Except

import TSLUtil
import Pos
import Name
import Frontend.Spec
import Frontend.NS
import Frontend.TVar
import Frontend.Type
import Frontend.TypeOps
import Frontend.Expr
import {-# SOURCE #-} Frontend.ExprOps

varMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> Var -> Var
varMapExpr f s v = Var (pos v) (varMem v) (tspecMapExpr f s $ tspec v) (name v) (fmap (mapExpr f s) $ varInit v)

varType :: (?spec::Spec, ?scope::Scope) => Var -> Type
varType = Type ?scope . tspec
