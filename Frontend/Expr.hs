{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Frontend.Expr(Expr(ETerm,ELit,EBool,EApply,EField,EPField,EIndex,ERange,ELength,EUnOp,EBinOp,ETernOp,ECase,ECond,ESlice,EStruct,EAtLab,ERel,ENonDet),
            ConstExpr, 
            LExpr,
            Slice,
            MethodRef(MethodRef),
            Radix(..),
            UOp(..),
            BOp(..),
            eAnd) where

import Prelude hiding ((<>))
import Text.PrettyPrint
import Data.List
import Data.Bits
import Numeric
import Data.Char

import TSLUtil
import Ops
import PP
import Pos
import Name

-- Common types
type Slice = (ConstExpr, ConstExpr) -- low,high

instance PP Slice where
    pp (l,h) = brackets $ pp l <> colon <> pp h 

data MethodRef = MethodRef Pos [Ident]

instance Eq MethodRef where
    (==) (MethodRef _ n1) (MethodRef _ n2) = n1 == n2

instance WithPos MethodRef where
    pos (MethodRef p _)     = p
    atPos (MethodRef _ m) p = MethodRef p m

instance PP MethodRef where
    pp (MethodRef _ m) = hcat $ punctuate (char '.') (map pp m)

instance Show MethodRef where
    show = render . pp

-- Expressions 
data Expr = ETerm   {epos::Pos, ssym::StaticSym}
          | ELit    {epos::Pos, width::Int, signed::Bool, rad::Radix, ival::Integer}
          | EBool   {epos::Pos, bval::Bool}
          | EApply  {epos::Pos, mref::MethodRef, args::[Maybe Expr]}
          | EField  {epos::Pos, struct::Expr, field::Ident}
          | EPField {epos::Pos, struct::Expr, field::Ident}
          | EIndex  {epos::Pos, arr::Expr, idx::Expr}
          | ERange  {epos::Pos, arr::Expr, range::(Expr, Expr)}
          | ELength {epos::Pos, arr::Expr}
          | EUnOp   {epos::Pos, uop::UOp, arg1::Expr}
          | EBinOp  {epos::Pos, bop::BOp, arg1::Expr, arg2::Expr}
          | ETernOp {epos::Pos, arg1::Expr, arg2::Expr, arg3::Expr}
          | ECase   {epos::Pos, caseexpr::Expr, cases::[(Expr, Expr)], def::(Maybe Expr)}
          | ECond   {epos::Pos, cases::[(Expr, Expr)], def::(Maybe Expr)}
          | ESlice  {epos::Pos, slexpr::Expr, slice::Slice}
          | EStruct {epos::Pos, typename::StaticSym, fields::(Either [(Ident, Expr)] [Expr])} -- either named or anonymous list of fields
          | EAtLab  {epos::Pos, lab::Ident}
          | ERel    {epos::Pos, rname::Ident, rargs::[Expr]}
          | ENonDet {epos::Pos, ndname::Maybe Ident{-internal use only-}}

instance Eq Expr where 
   (==) (ETerm _ s1)          (ETerm _ s2)          = s1 == s2
   (==) (ELit _ w1 s1 r1 v1)  (ELit _ w2 s2 r2 v2)  = w1 == w2 && s1 == s2 && v1 == v2
   (==) (EBool _ b1)          (EBool _ b2)          = b1 == b2
   (==) (EApply _ m1 as1)     (EApply _ m2 as2)     = m1 == m2 && as1 == as2
   (==) (EField _ e1 f1)      (EField _ e2 f2)      = e1 == e2 && f1 == f2
   (==) (EIndex _ a1 i1)      (EIndex _ a2 i2)      = a1 == a2 && i1 == i2
   (==) (ERange _ a1 (f1,l1)) (ERange _ a2 (f2,l2)) = a1 == a2 && f1 == f2 && l1 == l2
   (==) (ELength _ a1)        (ELength _ a2)        = a1 == a2
   (==) (EUnOp _ o1 e1)       (EUnOp _ o2 e2)       = o1 == o2 && e1 == e2
   (==) (EBinOp _ o1 x1 y1)   (EBinOp _ o2 x2 y2)   = o1 == o2 && x1 == x2 && y1 == y2
   (==) (ETernOp _ x1 y1 z1)  (ETernOp _ x2 y2 z2)  = x1 == x2 && y1 == y2 && z1 == z2
   (==) (ECase _ e1 cs1 d1)   (ECase _ e2 cs2 d2)   = e1 == e2 && cs1 == cs2 && d1 == d2
   (==) (ECond _ cs1 d1)      (ECond _ cs2 d2)      = cs1 == cs2 && d1 == d2
   (==) (ESlice _ e1 s1)      (ESlice _ e2 s2)      = e1 == e2 && s1 == s2
   (==) (EStruct _ t1 fs1)    (EStruct _ t2 fs2)    = t1 == t2 && fs1 == fs2
   (==) (EAtLab _ l1)         (EAtLab _ l2)         = l1 == l2
   (==) (ERel _ n1 as1)       (ERel _ n2 as2)       = n1 == n2 && as1 == as2
   (==) (ENonDet _ _)         (ENonDet _ _)         = True
   (==) _                     _                     = False



instance PP Expr where
    pp (ETerm _ s)               = pp s
    pp (ELit _ w s r v)          = ppInt w s r v
    pp (EBool _ True)            = text "true"
    pp (EBool _ False)           = text "false"
    pp (EApply _ m args)         = pp m <+> (parens $ hsep $ punctuate comma $ map pp args)
    pp (EIndex _ e i)            = pp e <> char '[' <> pp i <> char ']'
    pp (ERange _ e (f, l))       = pp e <> char '[' <> pp f <> text "##" <> pp l <> char ']'
    pp (ELength _ e)             = char '#' <> pp e
    pp (EField _ e f)            = pp e <> char '.' <> pp f
    pp (EPField _ e f)           = pp e <> text "->" <> pp f
    pp (EUnOp _ op e)            = parens $ pp op <> pp e
    pp (EBinOp _ op e1 e2)       = parens $ pp e1 <+> pp op <+> pp e2
    pp (ETernOp _ c e1 e2)       = parens $ pp c <+> char '?' <+> pp e2 <+> colon <+> pp e2
    pp (ECase _ e cs def)        = text "case" <+> (parens $ pp e) <+> (braces' $ ppcs $+$ ppdef)
                                   where ppcs = vcat $ map (\(c,e') -> pp c <> colon <+> pp e' <> semi) cs
                                         ppdef = text "default" <> colon <+> pp def <> semi
    pp (ECond _ cs def)          = text "cond" <+> (braces' $ ppcs $+$ ppdef)
                                   where ppcs = vcat $ map (\(c,e') -> pp c <> colon <+> pp e' <> semi) cs
                                         ppdef = text "default" <> colon <+> pp def <> semi
    pp (ESlice _ e s)            = pp e <> pp s
    pp (EStruct _ t (Left fs))   = pp t <+> (braces $ hcat $ punctuate comma $ 
                                             map (\(n,e) -> char '.' <> pp n <+> char '=' <+> pp e) fs)
    pp (EStruct _ t (Right fs))  = pp t <+> (braces' $ vcat $ punctuate comma $ map pp fs)
    pp (EAtLab _ l)              = char '@' <> pp l
    pp (ERel _ n as)             = char '?' <> pp n <+> (parens $ hsep $ punctuate comma $ map pp as)
    pp (ENonDet _ _)             = char '*'

instance Show Expr where
    show = render . pp

instance WithPos Expr where
    pos       = epos
    atPos e p = e{epos = p}

type ConstExpr = Expr

type LExpr = Expr

eAnd :: Pos -> [Expr] -> Expr
eAnd p [] = EBool p True
eAnd p es = foldl' (EBinOp p And) (head es) (tail es)
