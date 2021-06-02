module Abstract.BFormulaTypes (BoolBOp(..),
                      Formula(..),
                      bopToBoolOp,
                      boolOpToBOp) where

import Prelude hiding ((<>))

import Text.PrettyPrint

import Ops
import PP
import Abstract.Predicate

-- Logical operations
data BoolBOp = Conj 
             | Disj 
             | Impl
             | Equiv
             deriving (Eq)

bopToBoolOp :: BOp -> BoolBOp
bopToBoolOp And = Conj
bopToBoolOp Or  = Disj
bopToBoolOp Imp = Impl
bopToBoolOp Eq  = Equiv

instance PP BoolBOp where
    pp Conj  = text "&&"
    pp Disj  = text "||"
    pp Impl  = text "->"
    pp Equiv = text "<->"
    --pp = pp . boolOpToBOp

boolOpToBOp :: BoolBOp -> BOp
boolOpToBOp Conj  = And
boolOpToBOp Disj  = Or
boolOpToBOp Impl  = Imp
boolOpToBOp Equiv = Eq

-- Formula consists of predicates and boolean constants
-- connected with boolean connectors
data Formula = FTrue
             | FFalse
             | FBoolAVar AbsVar                   -- AVarBool or AVarPred
             | FEq       AbsVar AbsVar      -- AVarEnum or AVarInt
             | FEqConst  AbsVar Int
             | FBinOp    BoolBOp Formula Formula
             | FNot      Formula
             deriving (Eq)

instance PP Formula where
    pp FTrue             = text "true"
    pp FFalse            = text "false"
    pp (FBoolAVar v)     = pp v
    pp (FEq v1 v2)       = parens $ pp v1 <+> text "==" <+> pp v2
    pp (FEqConst v1 i)   = parens $ pp v1 <+> text "==" <+> pp i
    pp (FBinOp op f1 f2) = parens $ pp f1 <+> pp op <+> pp f2
    pp (FNot f)          = char '!' <> (parens $ pp f)

instance Show Formula where
    show = render . pp
