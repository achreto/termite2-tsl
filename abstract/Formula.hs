module Formula(BoolBOp(..),
               Formula(..),
               fdisj,
               fconj,
               bopToBoolOp,
               boolOpToBOp) where

import Predicate
import Common

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

boolOpToBOp :: BoolBOp -> BOp
boolOpToBOp Conj  = And
boolOpToBOp Disj  = Or
boolOpToBOp Impl  = Imp
boolOpToBOp Equiv = Eq

-- Formula consists of predicates and boolean constants
-- connected with boolean connectors
data Formula = FTrue
             | FFalse
             | FPred    Predicate
             | FBinOp   BoolBOp Formula Formula
             | FNot     Formula

fdisj :: [Formula] -> Formula
fdisj = error "Not implemented: fdisj"

fconj :: [Formula] -> Formula
fconj = error "Not implemented: fconj"
