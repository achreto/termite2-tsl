{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.TVarValidate(validateVar, 
                    validateVar2) where

import Control.Monad.Except

import TSLUtil
import Frontend.Spec
import Frontend.NS
import Frontend.TVar
import Frontend.TVarOps
import Frontend.Type
import Frontend.TypeOps
import Frontend.TypeValidate
import Frontend.ExprValidate
import Frontend.ExprOps

validateVar :: (?spec::Spec, MonadError String me) => Scope -> Var -> me ()
validateVar s v = do
    case tspec v of
         EnumSpec p _ -> err p $ "Enumeration declared inside variable declaration. Use typedef instead."
         _            -> return ()
    validateTypeSpec s (tspec v)

validateVar2 :: (?spec::Spec, MonadError String me) => Scope -> Var -> me ()
validateVar2 s v = do
    validateTypeSpec2 s (tspec v)
    case varInit v of
         Just e -> do let ?scope = s
                          ?privoverride = False
                      validateRegExpr' e
                      checkTypeMatch e (varType v) (exprType e)
         _      -> return ()


