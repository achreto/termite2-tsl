{-# LANGUAGE ImplicitParams, FlexibleContexts, UndecidableInstances #-}

module Frontend.Type(TypeSpec(BoolSpec,SIntSpec,UIntSpec,StructSpec,EnumSpec,PtrSpec,ArraySpec,VarArraySpec,SeqSpec,UserTypeSpec,TemplateTypeSpec, FlexTypeSpec), 
            WithTypeSpec(..),
            TypeDecl(TypeDecl), 
            Enumerator(Enumerator),
            Field(Field),
            arrLengthBits) where

import Prelude hiding ((<>))
import Text.PrettyPrint
import Control.Monad.Except

import PP
import Pos
import Name
import Frontend.Expr


arrLengthBits = 64::Int

-- Type spec
data Enumerator = Enumerator { epos    :: Pos
                             , ename   :: Ident}

instance PP Enumerator where
    pp (Enumerator _ n)  = pp n


instance WithPos Enumerator where
    pos       = epos
    atPos e p = e{epos = p}

instance WithName Enumerator where
    name = ename


-- Struct field
data Field = Field { fpos  :: Pos
                   , ftyp  :: TypeSpec
                   , fname :: Ident}

instance Eq Field where
    (==) (Field _ t1 n1) (Field _ t2 n2) = t1 == t2 && n1 == n2

instance PP Field where
    pp (Field _ t n) = pp t <+> pp n

instance WithPos Field where
    pos       = fpos
    atPos f p = f{fpos = p}

instance WithName Field where
    name = fname

instance WithTypeSpec Field where
    tspec = ftyp

data TypeSpec = BoolSpec         {tpos :: Pos}
              | SIntSpec         {tpos :: Pos, width  :: Int}
              | UIntSpec         {tpos :: Pos, width  :: Int}
              | StructSpec       {tpos :: Pos, fields :: [Field]}
              | EnumSpec         {tpos :: Pos, enums  :: [Enumerator]}
              | PtrSpec          {tpos :: Pos, ptype  :: TypeSpec}
              | ArraySpec        {tpos :: Pos, eltype :: TypeSpec, len :: Expr}
              | VarArraySpec     {tpos :: Pos, eltype :: TypeSpec}
              | SeqSpec          {tpos :: Pos, eltype :: TypeSpec}
              | UserTypeSpec     {tpos :: Pos, tname  :: StaticSym}
              | TemplateTypeSpec {tpos :: Pos, tmname :: Ident}
              | FlexTypeSpec     {tpos :: Pos}

-- Check exact syntactic equivalence of type specs
instance Eq TypeSpec where
    (==) (BoolSpec _)            (BoolSpec _)            = True
    (==) (SIntSpec _ i1)         (SIntSpec _ i2)         = i1 == i2
    (==) (UIntSpec _ i1)         (UIntSpec _ i2)         = i1 == i2
    (==) (StructSpec _ fs1)      (StructSpec _ fs2)      = fs1 == fs2
    (==) (EnumSpec _ es1)        (EnumSpec _ es2)        = False
    (==) (PtrSpec _ t1)          (PtrSpec _ t2)          = t1 == t2
    (==) (ArraySpec _ t1 l1)     (ArraySpec _ t2 l2)     = t1 == t2 && l1 == l2
    (==) (VarArraySpec _ t1)     (VarArraySpec _ t2)     = t1 == t2
    (==) (SeqSpec _ t1)          (SeqSpec _ t2)          = t1 == t2
    (==) (UserTypeSpec _ n1)     (UserTypeSpec _ n2)     = n1 == n2
    (==) (TemplateTypeSpec _ n1) (TemplateTypeSpec _ n2) = n1 == n2
    (==) _                       _                       = False


instance PP TypeSpec where
    pp (BoolSpec _)           = text "bool"
    pp (SIntSpec _ i)         = text "sint" <> char '<' <> pp i <> char '>'
    pp (UIntSpec _ i)         = text "uint" <> char '<' <> pp i <> char '>'
    pp (StructSpec _ fs)      = text "struct" <+> (braces $ nest' $ vcat $ map ((<> semi) . pp) fs)
    pp (EnumSpec _ es)        = text "enum" <+> (braces $ nest' $ vcat $ punctuate comma $ map pp es)
    pp (PtrSpec _ t)          = pp t <> char '*'
    pp (ArraySpec _ t l)      = pp t <> (brackets $ pp l)
    pp (VarArraySpec _ t)     = pp t <> (brackets empty)
    pp (SeqSpec _ t)          = pp t <+> text "seq"
    pp (UserTypeSpec _ n)     = pp n
    pp (TemplateTypeSpec _ n) = text "template" <+> pp n
    pp (FlexTypeSpec _)       = text "*"


instance Show TypeSpec where
    show = render . pp

instance WithPos TypeSpec where
    pos       = tpos
    atPos t p = t{tpos = p}

class WithTypeSpec a where
    tspec :: a -> TypeSpec

instance WithTypeSpec TypeSpec where
    tspec = id

-- Type declaration
data TypeDecl = TypeDecl { dpos  :: Pos
                         , dspec :: TypeSpec
                         , dname :: Ident}

instance PP TypeDecl where
    pp (TypeDecl _ t n) = text "typedef" <+> pp t <+> pp n <> semi

instance WithPos TypeDecl where
    pos       = dpos
    atPos t p = t{dpos=p}

instance WithName TypeDecl where
    name = dname

instance WithTypeSpec TypeDecl where
    tspec = dspec
