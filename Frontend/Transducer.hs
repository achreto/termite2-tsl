{-# LANGUAGE RecordWildCards #-}

module Frontend.Transducer(Transducer(Transducer, txInput, txOutput, txBody),
                           TxPort(TxPort, tpType, tpName),
                           TxPortRef(..),
                           TxInstance(TxInstance, tiTxName, tiInstName, tiInputs)) where
import Prelude hiding ((<>))
import Text.PrettyPrint

import PP
import Pos
import Name
import Frontend.Statement
import Frontend.Type


data TxPort = TxPort { tppos         :: Pos
                     , tpType        :: TypeSpec
                     , tpName        :: Ident
                     }

instance PP TxPort where
    pp TxPort{..} = pp tpType <+> pp tpName
    
instance Show TxPort where
    show      = render . pp

instance WithName TxPort where
    name = tpName

instance WithPos TxPort where
    pos       = tppos
    atPos i p = i{tppos = p}

instance WithTypeSpec TxPort where 
    tspec = tpType

data TxInstance = TxInstance { tipos      :: Pos
                             , tiTxName   :: Ident
                             , tiInstName :: Ident
                             , tiInputs   :: [Maybe TxPortRef]
                             }

instance PP TxInstance where
    pp TxInstance{..} = text "instance" <+> pp tiTxName <+> pp tiInstName 
                             <> (parens $ hsep $ punctuate comma $ map (maybe (pp "*") pp) tiInputs)
    
instance Show TxInstance where
    show      = render . pp

instance WithName TxInstance where
    name = tiInstName

instance WithPos TxInstance where
    pos       = tipos
    atPos i p = i{tipos = p}

data TxPortRef = TxInputRef Ident
               | TxLocalRef Ident Ident

instance PP TxPortRef where
    pp (TxInputRef p)   = pp p
    pp (TxLocalRef i p) = pp i <> char '.' <> pp p
    
instance Show TxPortRef where
    show      = render . pp

instance WithPos TxPortRef where
    pos  (TxInputRef p)   = pos p
    pos  (TxLocalRef i _) = pos i
    atPos _ _ = error "atPos TxPortRef"

data Transducer = Transducer { tpos            :: Pos
                             , txName          :: Ident
                             , txInput         :: [TxPort]
                             , txOutput        :: [TxPort]
                             , txBody          :: Either ([TxPortRef], [TxInstance]) Statement
                             }

instance PP Transducer where
    pp Transducer{..} = text "transducer" <+> pp txName <+> (parens $ hsep $ punctuate comma $ map pp txInput) 
                                          <+> text "->" <+> (parens $ hsep $ punctuate comma $ map pp txOutput)
                     $$ case txBody of
                             Left (rs, is) -> (pp "export" <+> (parens $ hsep $ punctuate comma $ map pp rs)) 
                                              $$ lbrace $$ (nest' $ vcat $ map pp is) $$ rbrace
                             Right s       -> pp s

instance Show Transducer where
    show      = render . pp

instance WithName Transducer where
    name = txName

instance WithPos Transducer where
    pos       = tpos
    atPos t p = t{tpos = p}
