{-# LANGUAGE ImplicitParams, UndecidableInstances #-}

module Frontend.Const(Const(Const,constVal)) where

import Prelude hiding ((<>))
import Text.PrettyPrint

import PP
import Pos
import Name
import Frontend.Expr
import Frontend.Type

data Const = Const { cpos     :: Pos
                   , ctyp     :: TypeSpec
                   , cname    :: Ident
                   , constVal :: ConstExpr}

instance PP Const where
    pp (Const _ t n e) = text "const" <+> pp t <+> pp n <+> char '=' <+> pp e <> semi

instance WithPos Const where
    pos       = cpos
    atPos c p = c{cpos = p}

instance WithName Const where
    name = cname

instance WithTypeSpec Const where
    tspec = ctyp
