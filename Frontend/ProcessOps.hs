{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.ProcessOps(validateProc) where

import Control.Monad.Except

import TSLUtil
import Name
import Frontend.Spec
import Frontend.Process
import Frontend.Template
import Frontend.Spec
import Frontend.StatementOps
import Frontend.StatementValidate
import Frontend.NS

validateProc :: (?spec::Spec, MonadError String me) => Template -> Process -> me ()
validateProc t p = do
    uniqNames (\n -> "Variable " ++ n ++ " declared multiple times in process " ++ sname p) 
              (procVar p)
    let ?privoverride = False in validateStat (ScopeProcess t p) (procStatement p)
