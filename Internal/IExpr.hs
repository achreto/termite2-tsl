{-# LANGUAGE ImplicitParams, TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Internal.IExpr(LVal(..),
             Val(..),
             GExpr(..),
             Expr,
             lvalToExpr,
             valSlice,
             valDefault,
             parseVal,
             exprType,
             exprWidth,
             exprSlice,
             exprScalars,
             exprVars,
             exprPad,
             (===),
             (/==),
             (==>),
             (.<=),
             (.%),
             uminus,
             disj,
             conj,
             neg,
             land,
             lor,
             plus,
             plusmod,
             econcat,
             true,
             false,
             Slice,
             isConstExpr,
             evalConstExpr,
             evalLExpr,
             isMemExpr,
             exprPtrSubexpr,
             arrLengthBits,
             mapExpr) where

import Prelude hiding ((<>))

import Data.Maybe
import Data.List
import Data.Bits hiding (isSigned)
import Text.PrettyPrint
import Control.Monad.Except
import qualified Text.Parsec as P

import Util
import Frontend.Grammar
import PP
import TSLUtil
import Ops
import Internal.IType
import Internal.IVar
import {-# SOURCE #-} Internal.ISpec
import Frontend.Type (arrLengthBits)

-- variable address
data LVal = LVar String
          | LField LVal String
          | LIndex LVal Integer
          | LSeqVal LVal
          deriving (Eq,Ord)

lvalToExpr :: LVal -> Expr 
lvalToExpr (LVar n)     = EVar n
lvalToExpr (LField s f) = EField (lvalToExpr s) f
lvalToExpr (LIndex a i) = EIndex (lvalToExpr a) (EConst $ UIntVal 32 i)

lvalType :: (?spec::Spec) => LVal -> Type
lvalType (LVar n)     = typ $ getVar n
lvalType (LField s n) = let Struct _ fs = lvalType s
                        in typ $ fromJust $ find (\(Field f _) -> n == f) fs 
lvalType (LSeqVal e)  = t where Seq _ t = lvalType e

instance PP LVal where
    pp (LVar n)     = pp n
    pp (LField s f) = pp s <> char '.' <> pp f
    pp (LIndex a i) = pp a <> char '[' <> pp i <> char ']'
    pp (LSeqVal e)  = char '[' <> pp e <> char ']'

-- Value
data Val = BoolVal   Bool
         | SIntVal   {ivalWidth::Int, ivalVal::Integer}
         | UIntVal   {ivalWidth::Int, ivalVal::Integer}
         | EnumVal   String
         | PtrVal    LVal
         | NullVal   Type
         deriving (Eq, Ord)

ivalIsSigned :: Val -> Bool
ivalIsSigned (SIntVal _ _) = True
ivalIsSigned (UIntVal _ _) = False

valType :: (?spec::Spec) => Val -> Type
valType (BoolVal _)   = Bool Nothing
valType (SIntVal w _) = SInt Nothing w
valType (UIntVal w _) = UInt Nothing w
valType (EnumVal n)   = Enum Nothing $ enumName $ getEnumerator n
valType (PtrVal a)    = Ptr Nothing $ lvalType a
valType (NullVal t)   = t

instance PP Val where
    pp (BoolVal True)  = text "true"
    pp (BoolVal False) = text "false"
    pp (SIntVal w v)   = ppInt w True  Rad16 v
    pp (UIntVal w v)   = ppInt w False Rad16 v
    pp (EnumVal n)     = text n
    pp (PtrVal a)      = char '&' <> pp a
    pp (NullVal _)     = text "NULL"

instance Show Val where
    show = render . pp

type Slice = (Int, Int)

instance PP Slice where
    pp (l,h) = brackets $ pp l <> colon <> pp h

-- Default value of a type
valDefault :: (?spec::Spec, Typed a) => a -> Val
valDefault x = case typ x of
                    Bool _       -> BoolVal False
                    SInt _ w     -> SIntVal w 0
                    UInt _ w     -> UIntVal w 0  
                    Enum _ n     -> EnumVal $ head $ enumEnums $ getEnumeration n
                    Struct _ _   -> error "valDefault Struct"
                    Ptr _ t      -> NullVal t
                    Array _ _ _  -> error "valDefault Array"


valSlice :: Val -> Slice -> Val
valSlice v (l,h) = UIntVal (h - l + 1)
                   $ foldl' (\a idx -> case testBit (ivalVal v) idx of
                                            True  -> a + bit (idx - l)
                                            False -> a)
                   0 [l..h]

parseVal :: (MonadError String me, ?spec::Spec) => Type -> String -> me Val
parseVal (SInt _ w) str = do
    (w',_,_,v) <- case P.parse litParser "" str of
                       Left e  -> throwError $ show e
                       Right x -> return x
    when  (w' > w) $ throwError $ "Width mismatch"
    return $ SIntVal w v 
parseVal (UInt _ w) str = do
    (w',s,_,v) <- case P.parse litParser "" str of
                       Left e  -> throwError $ show e
                       Right x -> return x
    when (w' > w) $ throwError $ "Width mismatch"
    when s $ throwError $ "Sign mismatch"
    return $ UIntVal w v 
parseVal (Bool _) str =
    case P.parse boolParser "" str of
         Left e  -> throwError $ show e
         Right b -> return $ BoolVal b
parseVal (Enum _ n) str = 
    case lookupEnumerator str of
         Nothing    -> throwError $ "Invalid enumerator: " ++ str
         Just enum  -> if' (enumName enum == n) (return $ EnumVal str)
                       $ throwError $ "Enumerator type mismatch" 

data GExpr v = EVar      v
             | EConst    Val
             | EField    (GExpr v) String
             | EIndex    (GExpr v) (GExpr v)
             | ERange    (GExpr v) (GExpr v, GExpr v)
             | ELength   (GExpr v)            -- Expr must be a VarArray
             | EUnOp     UOp (GExpr v)
             | EBinOp    BOp (GExpr v) (GExpr v)
             | ESlice    (GExpr v) Slice
             | ERel      String [GExpr v]
             deriving (Eq, Ord)

type Expr = GExpr String

instance (PP v) => PP (GExpr v) where
    pp (EVar n)          = pp n
    pp (EConst v)        = pp v
    pp (EField e f)      = pp e <> char '.' <> pp f
    pp (EIndex a i)      = pp a <> char '[' <> pp i <> char ']'
    pp (ERange a (f,l))  = pp a <> char '[' <> pp f <> text "##" <> pp l <> char ']'
    pp (ELength a)       = char '#' <> pp a
    pp (EUnOp op e)      = parens $ pp op <> pp e
    pp (EBinOp op e1 e2) = parens $ pp e1 <+> pp op <+> pp e2
    pp (ESlice e s)      = pp e <> pp s
    pp (ERel n as)       = char '?' <> pp n <> (parens $ hcat $ punctuate (text ", ") $ map pp as)

instance Show Expr where
    show = render . pp
    
exprType :: (?spec::Spec) => Expr -> Type
exprType (EVar n)                               = typ $ getVar n
exprType (EConst v)                             = valType v
exprType (EField s f)                           = let Struct _ fs = exprType s
                                                  in typ $ fromJust $ find (\(Field n _) -> n == f) fs 
exprType (EIndex a _)                           = case exprType a of
                                                       Array _ t _  -> t
                                                       VarArray _ t -> t
exprType (ERange a _)                           = case exprType a of
                                                       Array _ t _  -> VarArray Nothing t
                                                       VarArray _ t -> VarArray Nothing t
exprType (ELength _)                            = UInt Nothing arrLengthBits
exprType (EUnOp op e) | isArithUOp op           = if s 
                                                     then SInt Nothing w
                                                     else UInt Nothing w
                                                  where (s,w) = arithUOpType op (isSigned $ exprType e, exprWidth e)
exprType (EUnOp Not _)                          = Bool Nothing
exprType (EUnOp Deref e)                        = t where Ptr _ t = exprType e
exprType (EUnOp AddrOf e)                       = Ptr Nothing $ exprType e
exprType (EBinOp op e1 e2) | isRelBOp op        = Bool Nothing
                           | isBoolBOp op       = Bool Nothing
                           | isBitWiseBOp op    = exprType e1
                           | isArithBOp op      = if s 
                                                     then SInt Nothing w
                                                     else UInt Nothing w
                                                  where (s,w) = arithBOpType op (s1,w1) (s2,w2)
                                                        (s1,w1) = (isSigned $ exprType e1, exprWidth e1)
                                                        (s2,w2) = (isSigned $ exprType e1, exprWidth e2)
exprType (ESlice _ (l,h))                       = UInt Nothing $ h - l + 1
exprType (ERel _ _)                             = Bool Nothing

exprWidth :: (?spec::Spec) => Expr -> Int
exprWidth = typeWidth . exprType

-- TODO: optimise slicing of concatenations
exprSlice :: (?spec::Spec) => Expr -> Slice -> Expr
exprSlice e                      (l,h) | l == 0 && h == exprWidth e - 1 = e
exprSlice (ESlice e (l',_))      (l,h)                                  = exprSlice e (l'+l,l'+h)
exprSlice (EBinOp BConcat e1 e2) (l,h) | l > exprWidth e1 - 1           = exprSlice e2 (l - exprWidth e1, h - exprWidth e1)
                                       | h <= exprWidth e1 - 1          = exprSlice e1 (l,h)
                                       | otherwise                      = econcat [exprSlice e1 (l,exprWidth e1-1), exprSlice e2 (0, h - exprWidth e1)]
exprSlice e                      s                                      = ESlice e s

-- Extract all scalars from expression
exprScalars :: Expr -> Type -> [Expr]
exprScalars e (Struct _ fs)  = concatMap (\(Field n t) -> exprScalars (EField e n) t) fs
exprScalars e (Array _  t s) = concatMap (\i -> exprScalars (EIndex e (EConst $ UIntVal (bitWidth $ s-1) $ fromIntegral i)) t) [0..s-1]
exprScalars e (VarArray _ _) = error $ "exprScalars VarArray " ++ show e
exprScalars e _              = [e]

-- Variables involved in the expression
exprVars :: (?spec::Spec) => Expr -> [Var]
exprVars = nub . exprVars'

exprVars' :: (?spec::Spec) => Expr -> [Var]
exprVars' (EVar n)         = [getVar n]
exprVars' (EConst _)       = []
exprVars' (EField e _)     = exprVars' e
exprVars' (EIndex a i)     = exprVars' a ++ exprVars' i
exprVars' (ERange a (f,l)) = exprVars' a ++ exprVars' f ++ exprVars' l
exprVars' (ELength a)      = exprVars' a
exprVars' (EUnOp _ e)      = exprVars' e
exprVars' (EBinOp _ e1 e2) = exprVars' e1 ++ exprVars' e2
exprVars' (ESlice e _)     = exprVars' e
exprVars' (ERel _ as)      = concatMap exprVars' as

(===) :: Expr -> Expr -> Expr
e1 === e2 = EBinOp Eq e1 e2

(/==) :: Expr -> Expr -> Expr
e1 /== e2 = EBinOp Neq e1 e2

(==>) :: Expr -> Expr -> Expr
e1 ==> e2 = EBinOp Imp e1 e2

uminus :: Expr -> Expr
uminus = EUnOp UMinus

(.<=) :: Expr -> Expr -> Expr
e1 .<= e2 = EBinOp Lt e1 e2

disj :: [Expr] -> Expr
disj [] = false
disj es = foldl' (\e1 e2 -> if' (e1 == false) e2 $ if' (e2 == false) e1 $ if' ((e1 == true) || (e2 == true)) true $ EBinOp Or e1 e2) (head es) (tail es)

conj :: [Expr] -> Expr
conj [] = false
conj es = foldl' (\e1 e2 -> if' (e1 == true) e2 $ if' (e2 == true) e1 $ if' ((e1 == false) || (e2 == false)) false $ EBinOp And e1 e2) (head es) (tail es)

neg :: Expr -> Expr
neg = EUnOp Not

land :: Expr -> Expr -> Expr
land = EBinOp And

lor :: Expr -> Expr -> Expr
lor = EBinOp Or

plus :: [Expr] -> Expr
plus [e] = e
plus (e:es) = EBinOp Plus e $ plus es

(.%) :: Expr -> Expr -> Expr
(.%) e1 e2 = EBinOp Mod e1 e2

-- extend arguments to fit array index and sum them modulo array length
plusmod :: (?spec::Spec) => Expr -> [Expr] -> Expr
plusmod ar es = (plus $ map (exprPad w) es) .% EConst (UIntVal (bitWidth l) $ fromIntegral l)
    where Array _ _ l = exprType ar
          w = bitWidth (l-1)

exprPad :: (?spec::Spec) => Int -> Expr -> Expr
exprPad w e | exprWidth e >= w = e
            | otherwise        = econcat [e, EConst $ UIntVal (w - exprWidth e) 0]

-- TODO: merge adjacent expressions
econcat :: [Expr] -> Expr
econcat [e]        = e
econcat (e1:e2:es) = econcat $ (EBinOp BConcat e1 e2):es

true = EConst $ BoolVal True
false = EConst $ BoolVal False

-- Subexpressions dereferenced inside the expression
exprPtrSubexpr :: Expr -> [Expr]
exprPtrSubexpr (EField e _)     = exprPtrSubexpr e
exprPtrSubexpr (EIndex a i)     = exprPtrSubexpr a ++ exprPtrSubexpr i
exprPtrSubexpr (ERange a (f,l)) = exprPtrSubexpr a ++ exprPtrSubexpr f ++ exprPtrSubexpr l
exprPtrSubexpr (ELength a)      = exprPtrSubexpr a
exprPtrSubexpr (EUnOp Deref e)  = e:(exprPtrSubexpr e)
exprPtrSubexpr (EUnOp _ e)      = exprPtrSubexpr e
exprPtrSubexpr (EBinOp _ e1 e2) = exprPtrSubexpr e1 ++ exprPtrSubexpr e2
exprPtrSubexpr (ESlice e _)     = exprPtrSubexpr e
exprPtrSubexpr (ERel _ as)      = concatMap exprPtrSubexpr as
exprPtrSubexpr _                = []

isConstExpr :: Expr -> Bool
isConstExpr (EVar _)         = False
isConstExpr (EConst _)       = True
isConstExpr (EField e _)     = isConstExpr e
isConstExpr (EIndex a i)     = isConstExpr a && isConstExpr i
isConstExpr (ERange a (f,l)) = all isConstExpr [a,f,l]
isConstExpr (ELength _)      = False
isConstExpr (EUnOp AddrOf e) = isConstLExpr e
isConstExpr (EUnOp _ e)      = isConstExpr e
isConstExpr (EBinOp _ e1 e2) = isConstExpr e1 && isConstExpr e2
isConstExpr (ESlice e _)     = isConstExpr e
isConstExpr (ERel _ _)       = False -- even if all args are constant, it may not evaluate to a constant

isConstLExpr :: Expr -> Bool
isConstLExpr (EVar _)     = True
isConstLExpr (EField s _) = isConstLExpr s
isConstLExpr (EIndex a i) = isConstLExpr a && isConstExpr i

evalConstExpr :: Expr -> Val
evalConstExpr (EConst v)                         = v
evalConstExpr (EUnOp op e) | isArithUOp op       = case s of
                                                        True  -> SIntVal w v
                                                        False -> UIntVal w v
                                                   where val     = evalConstExpr e
                                                         (v,s,w) = arithUOp op (ivalVal val,ivalIsSigned val,ivalWidth val)
evalConstExpr (EUnOp Not e)                      = BoolVal $ not b
                                                   where BoolVal b = evalConstExpr e
evalConstExpr (EUnOp AddrOf e)                   = PtrVal $ evalLExpr e
evalConstExpr (EBinOp op e1 e2) | isArithBOp op  = case s of
                                                        True  -> SIntVal w v
                                                        False -> UIntVal w v
                                                   where val1    = evalConstExpr e1
                                                         val2    = evalConstExpr e2
                                                         (v,s,w) = arithBOp op (ivalVal val1, ivalIsSigned val1, ivalWidth val1)
                                                                               (ivalVal val2, ivalIsSigned val2, ivalWidth val2)
evalConstExpr (EBinOp op e1 e2) | elem op [Eq,Neq,Lt,Gt,Lte,Gte,And,Or,Imp] = 
                                                   case v1 of
                                                        BoolVal _ -> case op of
                                                                          Eq  -> BoolVal $ b1 == b2
                                                                          Neq -> BoolVal $ b1 /= b2
                                                                          And -> BoolVal $ b1 && b2
                                                                          Or  -> BoolVal $ b1 || b2
                                                                          Imp -> BoolVal $ (not b1) || b2
                                                        EnumVal _ -> case op of
                                                                          Eq  -> BoolVal $ en1 == en2
                                                                          Neq -> BoolVal $ en1 /= en2
                                                        _         -> case op of
                                                                          Eq  -> BoolVal $ i1 == i2
                                                                          Neq -> BoolVal $ i1 /= i2
                                                                          Lt  -> BoolVal $ i1 < i2
                                                                          Gt  -> BoolVal $ i1 > i2
                                                                          Lte -> BoolVal $ i1 <= i2
                                                                          Gte -> BoolVal $ i1 >= i2
                                                   where v1 = evalConstExpr e1
                                                         v2 = evalConstExpr e2
                                                         BoolVal b1  = v1
                                                         BoolVal b2  = v2
                                                         EnumVal en1 = v1
                                                         EnumVal en2 = v2
                                                         i1 = ivalVal v1
                                                         i2 = ivalVal v2
evalConstExpr (ESlice e s)     = valSlice (evalConstExpr e) s

evalLExpr :: Expr -> LVal
evalLExpr (EVar n)     = LVar n
evalLExpr (EField s f) = LField (evalLExpr s) f
evalLExpr (EIndex a i) = LIndex (evalLExpr a) (ivalVal $ evalConstExpr i)

isMemExpr :: (?spec::Spec) => Expr -> Bool
isMemExpr (EVar n)     = varMem $ getVar n
isMemExpr (EField s _) = isMemExpr s
isMemExpr (EIndex a _) = isMemExpr a
isMemExpr (ERange a _) = isMemExpr a
isMemExpr (ESlice e _) = isMemExpr e
isMemExpr _            = False

mapExpr :: (Expr -> Expr) -> Expr -> Expr
mapExpr f e0 = case f e0 of
                    e@(EVar _)      -> e
                    e@(EConst _)    -> e
                    EField e n      -> EField (mapExpr f e) n
                    EIndex a i      -> EIndex (mapExpr f a) (mapExpr f i)
                    ERange a (fr,l) -> ERange (mapExpr f a) (mapExpr f fr, mapExpr f l)
                    ELength a       -> ELength (mapExpr f a)
                    EUnOp op e      -> EUnOp op (mapExpr f e)
                    EBinOp op e1 e2 -> EBinOp op (mapExpr f e1) (mapExpr f e2)
                    ESlice e s      -> ESlice (mapExpr f e) s
                    ERel n as       -> ERel n $ map (mapExpr f) as
