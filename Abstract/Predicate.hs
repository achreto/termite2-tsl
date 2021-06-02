{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Abstract.Predicate(PVarOps,
                 bavarAVar,
                 avarBAVar,
                 AbsVar(..),
                 avarWidth,
                 avarRange,
                 avarIsPred,
                 avarIsRelPred,
                 avarIsEnum,
                 avarCategory,
                 avarVar,
                 avarTerms,
                 avarToExpr,
                 avarValToConst,
                 ArithUOp(..),
                 uopToArithOp,
                 arithOpToUOp,
                 ArithBOp(..),
                 bopToArithOp,
                 arithOpToBOp,
                 Term(..),
                 PTerm(..),
                 ptermTerm,
                 termType,
                 termWidth,
                 termCategory,
                 termVar,
                 evalConstTerm,
                 isConstTerm,
                 RelOp(..),
                 bopToRelOp,
                 relOpToBOp,
                 relOpNeg,
                 relOpSwap,
                 PredOp(..),
                 relOpToPredOp,
                 Predicate(..),
                 predCategory,
                 predVar,
                 predToExpr,
                 termToExpr,
                 ) where

import Prelude hiding ((<>))

import Text.PrettyPrint
import Data.List
import Data.Bits

import Util
import TSLUtil
import PP
import Ops
import Internal.ISpec
import Internal.IExpr
import Internal.IVar
import Internal.IType
import Synthesis.Interface hiding(getVar)

type PVarOps pdb s u = VarOps pdb (BAVar AbsVar AbsVar) s u

bavarAVar :: BAVar AbsVar AbsVar -> AbsVar
bavarAVar (StateVar av _) = av
bavarAVar (LabelVar av _) = av
bavarAVar (OutVar   av _) = av

avarBAVar :: (?spec::Spec) => AbsVar -> BAVar AbsVar AbsVar
avarBAVar av | avarCategory av == VarTmp   = LabelVar av (avarWidth av)
avarBAVar av | avarCategory av == VarState = StateVar av (avarWidth av)

data AbsVar = AVarPred Predicate   -- predicate variable
            | AVarEnum Term        -- unabstracted Enum scalar variable
            | AVarBool Term        -- unabstracted Bool variable
            | AVarInt  Term        -- unabstracted integral variable
            deriving(Eq, Ord)

avarWidth :: (?spec::Spec) => AbsVar -> Int
avarWidth (AVarPred _) = 1
avarWidth (AVarEnum t) = termWidth t
avarWidth (AVarBool _) = 1
avarWidth (AVarInt  t) = termWidth t

avarRange :: (?spec::Spec) => AbsVar -> Int
avarRange (AVarPred _) = 1
avarRange (AVarEnum t) = let Enum _ n = termType t in
                         (length $ enumEnums $ getEnumeration n) - 1
avarRange (AVarBool _) = 1
avarRange (AVarInt  t) = (1 `shiftL` (termWidth t)) - 1

avarCategory :: (?spec::Spec) => AbsVar -> VarCategory
avarCategory (AVarPred p) = predCategory p
avarCategory (AVarEnum t) = termCategory t
avarCategory (AVarBool t) = termCategory t
avarCategory (AVarInt  t) = termCategory t

avarIsPred :: AbsVar -> Bool
avarIsPred (AVarPred _) = True
avarIsPred _            = False

avarIsRelPred :: AbsVar -> Bool
avarIsRelPred (AVarPred (PRel _ _)) = True
avarIsRelPred _                     = False

avarIsEnum :: AbsVar -> Bool
avarIsEnum (AVarEnum _) = True
avarIsEnum _            = False

avarVar :: (?spec::Spec) => AbsVar -> [Var]
avarVar (AVarPred p) = predVar p
avarVar (AVarEnum t) = termVar t
avarVar (AVarBool t) = termVar t
avarVar (AVarInt  t) = termVar t

avarTerms :: AbsVar -> [Term]
avarTerms = nub . avarTerms' 

avarTerms' :: AbsVar -> [Term]
avarTerms' (AVarPred p) = predTerm p
avarTerms' (AVarEnum t) = [t]
avarTerms' (AVarInt  t) = [t]
avarTerms' (AVarBool t) = [t]

avarToExpr :: (?spec::Spec) => AbsVar -> Expr
avarToExpr (AVarPred p) = predToExpr p
avarToExpr (AVarEnum t) = termToExpr t
avarToExpr (AVarBool t) = termToExpr t
avarToExpr (AVarInt  t) = termToExpr t

avarValToConst :: (?spec::Spec) => AbsVar -> Int -> Val
avarValToConst av i = case exprType $ avarToExpr av of
                           Bool _   -> if' (i==0) (BoolVal False) (BoolVal True)
                           UInt _ w -> UIntVal w (fromIntegral i)
                           SInt _ w -> SIntVal w (fromIntegral i)
                           Enum _ n -> EnumVal $ (enumEnums $ getEnumeration n) !! i


instance PP AbsVar where
    pp (AVarPred p) = pp p
    pp (AVarEnum t) = pp t
    pp (AVarBool t) = pp t
    pp (AVarInt  t) = pp t

instance Show AbsVar where
    show = render . pp

-- Arithmetic operations
data ArithUOp = AUMinus 
              | ABNeg
              deriving (Eq,Ord)

uopToArithOp :: UOp -> ArithUOp
uopToArithOp UMinus = AUMinus
uopToArithOp BNeg   = ABNeg

arithOpToUOp :: ArithUOp -> UOp 
arithOpToUOp AUMinus = UMinus
arithOpToUOp ABNeg   = BNeg

data ArithBOp = ABAnd 
              | ABOr 
              | ABXor
              | ABConcat
              | APlus 
              | ABinMinus 
              | AMod
              | AMul
              deriving(Eq,Ord)

bopToArithOp :: BOp -> ArithBOp
bopToArithOp BAnd       = ABAnd       
bopToArithOp BOr        = ABOr 
bopToArithOp BXor       = ABXor
bopToArithOp BConcat    = ABConcat
bopToArithOp Plus       = APlus 
bopToArithOp BinMinus   = ABinMinus 
bopToArithOp Mod        = AMod
bopToArithOp Mul        = AMul

arithOpToBOp :: ArithBOp -> BOp
arithOpToBOp ABAnd      = BAnd       
arithOpToBOp ABOr       = BOr 
arithOpToBOp ABXor      = BXor
arithOpToBOp ABConcat   = BConcat
arithOpToBOp APlus      = Plus 
arithOpToBOp ABinMinus  = BinMinus 
arithOpToBOp AMod       = Mod
arithOpToBOp AMul       = Mul


-- Arithmetic (scalar) term
data Term = TVar    String
          | TSInt   Int Integer
          | TUInt   Int Integer
          | TEnum   String
          | TTrue
          | TAddr   Term
          | TField  Term String
          | TIndex  Term Term
          | TUnOp   ArithUOp Term
          | TBinOp  ArithBOp Term Term
          | TSlice  Term (Int,Int)
          deriving (Eq,Ord)

termType :: (?spec::Spec) => Term -> Type
termType = exprType . termToExpr

instance PP Term where
    pp = pp . termToExpr

instance Show Term where
    show = render . pp

termVar :: (?spec::Spec) => Term -> [Var]
termVar = exprVars . termToExpr

evalConstTerm :: Term -> Val
evalConstTerm = evalConstExpr . termToExpr

--termSimplify :: Term -> Term
--termSimplify = scalarExprToTerm . exprSimplify . termToExpr



termCategory :: (?spec::Spec) => Term -> VarCategory
termCategory t = if any ((==VarTmp) . varCat) $ termVar t
                    then VarTmp
                    else VarState

termWidth :: (?spec::Spec) => Term -> Int
termWidth = typeWidth . termType

--termWidth :: (?spec::Spec) => Term -> Int
--termWidth t = case typ t of
--                   Ptr _    -> 64
--                   Bool     -> 1
--                   Enum n   -> bitWidth $ (length $ enumEnums $ getEnumeration n) - 1
--                   (UInt w) -> w
--                   (SInt w) -> w

-- Subset of terms that can be used in a predicate: int's, and pointers
-- (no structs, arrays, or bools)
data PTerm = PTInt Term
           | PTPtr Term
           deriving (Eq, Ord)

ptermTerm :: PTerm -> Term
ptermTerm (PTInt t) = t
ptermTerm (PTPtr t) = t

ptermType :: (?spec::Spec) => PTerm -> Type
ptermType = termType . ptermTerm

instance PP PTerm where
    pp = pp . ptermTerm

instance Show PTerm where
    show = render . pp


-- Relational operations
data RelOp = REq
           | RNeq 
           | RLt 
           | RGt 
           | RLte 
           | RGte
           deriving (Eq,Ord)

instance PP RelOp where
    pp = pp . relOpToBOp

instance Show RelOp where
    show = render . pp

bopToRelOp :: BOp -> RelOp
bopToRelOp Eq  = REq
bopToRelOp Neq = RNeq
bopToRelOp Lt  = RLt
bopToRelOp Gt  = RGt
bopToRelOp Lte = RLte
bopToRelOp Gte = RGte

relOpToBOp :: RelOp -> BOp
relOpToBOp REq  = Eq
relOpToBOp RNeq = Neq
relOpToBOp RLt  = Lt
relOpToBOp RGt  = Gt
relOpToBOp RLte = Lte
relOpToBOp RGte = Gte

relOpNeg :: RelOp -> RelOp
relOpNeg REq  = RNeq
relOpNeg RNeq = REq
relOpNeg RLt  = RGte
relOpNeg RGt  = RLte
relOpNeg RLte = RGt
relOpNeg RGte = RLt

-- swap sides
relOpSwap :: RelOp -> RelOp
relOpSwap REq  = REq
relOpSwap RNeq = RNeq
relOpSwap RLt  = RGt
relOpSwap RGt  = RLt
relOpSwap RLte = RGte
relOpSwap RGte = RLte

data PredOp = PEq
            | PLt
            | PLte
            deriving (Eq, Ord)

relOpToPredOp :: RelOp -> (Bool, PredOp)
relOpToPredOp REq  = (True,  PEq)
relOpToPredOp RNeq = (False, PEq)
relOpToPredOp RLt  = (True,  PLt)
relOpToPredOp RGt  = (False, PLt)
relOpToPredOp RLte = (True,  PLte)
relOpToPredOp RGte = (False, PLte)

instance PP PredOp where
    pp PEq          = text "=="
    pp PLt          = text "<"
    pp PLte         = text "<="

instance Show PredOp where
    show = render . pp

-- Predicates
data Predicate = PAtom {pOp  :: PredOp, pTerm1 :: PTerm, pTerm2 :: PTerm}
               | PRel  {pRel :: String, pArgs :: [Expr]}
               deriving (Eq, Ord)

instance PP Predicate where
    pp (PAtom op t1 t2) = pp t1 <> pp op <> pp t2
    pp (PRel  rel as)   = text rel <> (parens $ hcat $ punctuate (text ",") $ map pp as)

instance Show Predicate where
    show = render . pp

predTerm :: Predicate -> [Term]
predTerm (PAtom _ t1 t2) = map ptermTerm [t1,t2]
predTerm (PRel  _ _)     = []

predVar :: (?spec::Spec) => Predicate -> [Var]
predVar p@PAtom{..} = nub $ concatMap termVar $ predTerm p
predVar   PRel{..}  = nub $ concatMap exprVars pArgs

predCategory :: (?spec::Spec) => Predicate -> VarCategory
predCategory p = if any ((==VarTmp) . varCat) $ exprVars $ predToExpr p
                    then VarTmp
                    else VarState


termToExpr :: Term -> Expr
termToExpr (TVar n)          = EVar   n
termToExpr (TUInt w i)       = EConst (UIntVal w i)
termToExpr (TSInt w i)       = EConst (SIntVal w i)
termToExpr (TEnum  e)        = EConst (EnumVal e)
termToExpr TTrue             = EConst (BoolVal True)
termToExpr (TAddr t)         = EUnOp  AddrOf (termToExpr t)
termToExpr (TField s f)      = EField (termToExpr s) f
termToExpr (TIndex a i)      = EIndex (termToExpr a) (termToExpr i)
termToExpr (TUnOp op t)      = EUnOp (arithOpToUOp op) (termToExpr t)
termToExpr (TBinOp op t1 t2) = EBinOp (arithOpToBOp op) (termToExpr t1) (termToExpr t2)
termToExpr (TSlice t s)      = ESlice (termToExpr t) s

ptermToExpr :: PTerm -> Expr 
ptermToExpr = termToExpr . ptermTerm

isConstTerm :: Term -> Bool
isConstTerm = isConstExpr . termToExpr

predToExpr :: Predicate -> Expr
predToExpr (PAtom PEq  t1 t2) = EBinOp Eq  (ptermToExpr t1) (ptermToExpr t2)
predToExpr (PAtom PLt  t1 t2) = EBinOp Lt  (ptermToExpr t1) (ptermToExpr t2)
predToExpr (PAtom PLte t1 t2) = EBinOp Lte (ptermToExpr t1) (ptermToExpr t2)
predToExpr (PRel  rel  as)    = ERel rel as
