{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, FlexibleContexts #-}

module Frontend.TransducerValidate(validateTxNS,validateTxImplementation2) where

import Data.List
import Control.Monad.Except
import Data.Maybe

import Util hiding (name)
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
import Frontend.Type

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
validateTxConnections tx@Transducer{txBody=Left (es,is)} = do
    -- every instance input refers to another local instance or global input of 
    -- the matching type
    mapIdxM_ (\inst iid -> do
        x <- checkTransducer (tiTxName inst)
        mapIdxM_ (\mi id -> when (isJust mi) $ do let t = Type ScopeTop $ tspec $ txInput x !! id
                                                  p <- txCheckPort tx (fromJust mi)
                                                  let t' = Type ScopeTop $ tspec p
                                                  checkTypeMatch (fromJust mi) t t')
                 $ tiInputs inst)
             $ is
    -- typecheck exports
    mapM_ (\(ref, port) -> do port' <- txCheckPort tx ref
                              let t = Type ScopeTop $ tspec port
                                  t' = Type ScopeTop $ tspec port'
                              checkTypeMatch ref t t')
          $ zip es (txOutput tx)
    -- TODO: no circular connections

validateTxStatement :: (?spec::Spec, MonadError String me) => Transducer -> me ()
validateTxStatement t@Transducer{txBody=Right s,..} = do
    let ?privoverride = False
    let ?scope = ScopeTransducer t
    validateStat' False s
    -- No sequences in local variables
    mapM_ (\v -> assert (not $ isSeqContainer $ varType v) (pos v) $ "Local variable of a transducer must not be (or contain) a sequence")
          $ stmtVar s
