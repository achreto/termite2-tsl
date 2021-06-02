{-# LANGUAGE ImplicitParams, RecordWildCards, FlexibleContexts #-}

module Frontend.TransducerOps(txLocalDecls, txLookupPort, txGetPort, txCheckPort) where

import Control.Monad.Except
import Data.Maybe
import Data.List

import TSLUtil
import Pos
import Frontend.Spec
import Frontend.NS
import Frontend.Transducer
import Frontend.Statement

txLocalDecls :: (?spec::Spec) => Transducer -> [Obj]
txLocalDecls t = (map (ObjTxInput t) (txInput t))   ++
                 (map (ObjTxOutput t) (txOutput t)) ++
                 case txBody t of
                      Left (_,is) -> map (ObjTxInstance t) is
                      Right s     -> map (ObjVar (ScopeTransducer t)) (stmtVar s)     

txLookupPort :: (?spec::Spec) =>  Transducer -> TxPortRef -> Maybe TxPort
txLookupPort Transducer{..} (TxInputRef n) = find ((== n). tpName) txInput
txLookupPort x (TxLocalRef i n) = 
    case txBody x of
         Left (_,is) -> case find ((== i) . tiInstName) is of
                             Nothing   -> Nothing
                             Just inst -> let x' = getTransducer $ tiTxName inst 
                                          in find ((==n) . tpName) $ txOutput x'
         Right _     -> Nothing

txGetPort :: (?spec::Spec) => Transducer -> TxPortRef -> TxPort
txGetPort x ref = fromJust $ txLookupPort x ref

txCheckPort :: (?spec::Spec, MonadError String me) => Transducer -> TxPortRef -> me TxPort
txCheckPort x ref = 
    case txLookupPort x ref of
         Nothing -> err (pos ref) $ "Unknown port: " ++ show ref
         Just p  -> return p
