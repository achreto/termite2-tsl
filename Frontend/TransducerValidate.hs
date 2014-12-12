{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards #-}

module Frontend.TransducerValidate(validateTxNS,validateTxImplementation2) where

import Data.List
import Control.Monad.Error
import Data.Maybe

import Pos
import Name
import TSLUtil
import Frontend.Spec
import Frontend.NS
import Frontend.Transducer
import Frontend.TransducerOps
import Frontend.Statement
import Frontend.StatementValidate
import Frontend.TypeOps
import Frontend.TVarOps

validateTxNS :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxNS t = do
    let ns = txLocalDecls t
    uniqNames (\n -> "Identifier " ++ n ++ " declared multiple times in transducer " ++ sname t) ns
    case mapMaybe (\o -> fmap (o,) $ find (\o' -> name o' == name o) specNamespace) ns of
         []       -> return ()
         (o,o'):_ -> err (pos o) $ "Identifier " ++ sname o ++ " conflicts with global declaration at " ++ spos o'

validateTxImplementation2 :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxImplementation2 t = do
    case txBody t of
         Left is -> validateTxConnections t
         Right s -> validateTxStatement t

validateTxConnections :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxConnections Transducer{txBody=Left is,..} = error "validateTxConnections not implemented"

validateTxStatement :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxStatement t@Transducer{txBody=Right s,..} = do
    let ?privoverride = False
    let ?scope = ScopeTransducer t
    validateStat' False s
    -- No sequences in local variables
    mapM_ (\v -> assert (not $ isSeqContainer $ varType v) (pos v) $ "Local variable of a transducer must not be (or contain) a sequence")
          $ stmtVar s
