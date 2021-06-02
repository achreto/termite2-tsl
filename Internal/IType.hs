module Internal.IType(Field(..),
             Type(..),
             Typed(..),
             isSigned,
             isInt,
             isBool,
             isPtr,
             isSeq,
             isEnum,
             isScalar,
             Enumeration(..)) where

import Prelude hiding ((<>))
import Text.PrettyPrint

import PP
import TSLUtil

data Field = Field String Type deriving (Eq,Ord)

instance PP Field where
    pp (Field n t) = pp t <+> text n

instance Typed Field where
    typ (Field _ t) = t

type MString = Maybe String

data Type = Bool     MString 
          | SInt     MString Int
          | UInt     MString Int
          | Enum     MString String
          | Struct   MString [Field]
          | Ptr      MString Type
          | Seq      MString Type
          | Array    MString Type Int
          | VarArray MString Type
          deriving (Eq,Ord)

instance PP Type where
    pp (Bool _)       = text "bool"
    pp (SInt _ i)     = text "sint" <> char '<' <> pp i <> char '>'
    pp (UInt _ i)     = text "uint" <> char '<' <> pp i <> char '>'
    pp (Enum _ e)     = text e
    pp (Struct _ fs)  = text "struct" <+> (braces $ nest' $ vcat $ map ((<> semi) . pp) fs)
    pp (Ptr _ t)      = pp t <> char '*'
    pp (Seq _ t)      = pp t <+> text "seq"
    pp (Array _ t l)  = pp t <> char '[' <> pp l <> char ']'
    pp (VarArray _ t) = pp t <> char '[' <> char ']'

instance Show Type where
    show = render . pp

class Typed a where
    typ :: a -> Type

instance Typed Type where
    typ = id

isSigned :: (Typed a) => a -> Bool
isSigned x = case typ x of
                  SInt _ _ -> True
                  UInt _ _ -> False


isInt :: (Typed a) => a -> Bool
isInt x = case typ x of
               SInt _ _ -> True
               UInt _ _ -> True
               _      -> False

isEnum :: (Typed a) => a -> Bool
isEnum x = case typ x of
                Enum _ _ -> True
                _        -> False

isPtr :: (Typed a) => a -> Bool
isPtr x = case typ x of
               Ptr _ _ -> True
               _       -> False

isBool :: (Typed a) => a -> Bool
isBool x = case typ x of
                Bool _ -> True 
                _      -> False

isSeq :: (Typed a) => a -> Bool
isSeq x = case typ x of
               Seq _ _ -> True
               _       -> False

isScalar :: (Typed a) => a -> Bool
isScalar x = case typ x of
                  Bool _   -> True
                  SInt _ _ -> True
                  UInt _ _ -> True
                  Enum _ _ -> True
                  Ptr  _ _ -> True
                  _      -> False

data Enumeration = Enumeration { enumName  :: String
                               , enumEnums :: [String]
                               }

instance PP Enumeration where
    pp (Enumeration n es) = text "enum" <+> text n <+> 
                            (braces' $ vcat $ map ((<> semi) . text) es)
