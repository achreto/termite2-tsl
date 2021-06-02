{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.ConstOps(validateConst,
                validateConst2) where

import Control.Monad.Except

import TSLUtil
import Pos
import Frontend.Type
import Frontend.TypeOps
import Frontend.TypeValidate
import Frontend.ExprOps
import Frontend.ExprValidate
import Frontend.Const
import Frontend.Spec
import Frontend.NS

constType :: (?spec::Spec,?scope::Scope) => Const -> Type
constType = Type ?scope . tspec

-- First pass: validate types
validateConst :: (?spec::Spec, MonadError String me) => Scope -> Const -> me ()
validateConst s c = validateTypeSpec s (tspec c)

-- Second pass: validate value expressions
validateConst2 :: (?spec::Spec, MonadError String me) => Scope -> Const -> me ()
validateConst2 s c = do
    let ?scope = s
        ?privoverride = False
    let v = constVal c
    validateTypeSpec2 s (tspec c)
    validateExpr' v
    checkTypeMatch v (constType c) (exprType v)
    assert (isConstExpr v) (pos v) $ "Non-constant expression in constant declaration"
