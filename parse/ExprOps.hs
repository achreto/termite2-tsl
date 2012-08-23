{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module ExprOps(evalInt) where

import Control.Monad.Error
import Data.Maybe

import TSLUtil
import Pos
import Name
import Template
import TypeSpec
import TypeSpecOps
import Expr
import Spec
import Method
import NS

evalInt :: (?spec::Spec) => Scope -> ConstExpr -> Integer
evalInt = error "evalInt not implemented"

isLExpr :: (?spec::Spec) => Scope -> Expr -> Bool
isLExpr s e = error "isLExpr not implemented"

-- Assumes that expression has been validated first
instance (?spec::Spec,?scope::Scope) => WithType Expr where
    typ (ETerm   _ n)           = typ $ getTerm ?scope n
    typ (ELit    p w True _ _)  = (SIntSpec p w,?scope)
    typ (ELit    p w False _ _) = (UIntSpec p w,?scope)
    typ (EBool   p _)           = (BoolSpec p  ,?scope)
    typ (EApply  _ mref _)      = (fromJust $ methRettyp m,s) where (m,s) = getMethod ?scope mref
    typ (EField  _ e f)         = typ $ objGet (ObjType $ typ e) f 
    typ (EPField _ e f)         = typ $ objGet (ObjType (t,s)) f where (PtrSpec _ t,s) = typ' e
    typ (EIndex  _ e i)         = (t,s) where (ArraySpec _ t _,s) = typ' e
    typ (EUnOp   _ UMinus e)    = case typ' e of
                                       t@(SIntSpec p w, s) -> t
                                       (UIntSpec p w, s)   -> (SIntSpec p w, s)
    typ (EUnOp   p Not e)       = (BoolSpec p,?scope)
    typ (EUnOp   _ BNeg e)      = typ e
    typ (EUnOp   _ Deref e)     = (t,s) where (PtrSpec _ t,s) = typ' e
    typ (EUnOp   p AddrOf e)    = (PtrSpec p t,s) where (t,s) = typ' e

    typ (EBinOp  p op e1 e2) | elem op [Eq,Neq,Lt,Gt,Lte,Gte,And,Or,Imp] = (BoolSpec p,?scope)
                             | elem op [BAnd,BOr,BXor] = typ e1
                             | elem op [Plus,Mul] = case (tspec e1, tspec e2) of
                                                         ((UIntSpec _ w1), (UIntSpec _ w2)) -> (UIntSpec p (max w1 w2),?scope)
                                                         _                                  -> (SIntSpec p (max (typeWidth e1) (typeWidth e2)),?scope)
                             | op == BinMinus = (SIntSpec p (max (typeWidth e1) (typeWidth e2)),?scope)
                             | op == Mod = typ e1

--          | ETernOp {epos::Pos, arg1::Expr, arg2::Expr, arg3::Expr}
--          | ECase   {epos::Pos, caseexpr::Expr, cases::[(Expr, Expr)], def::(Maybe Expr)}
--          | ECond   {epos::Pos, cases::[(Expr, Expr)], def::(Maybe Expr)}
--          | ESlice  {epos::Pos, slexpr::Expr, slice::Slice}
--          | EStruct {epos::Pos, typename::StaticSym, fields::(Either [(Ident, Expr)] [Expr])} -- either named or anonymous list of fields
--          | ENonDet {epos::Pos}


instance (?spec::Spec,?scope::Scope) => WithTypeSpec Expr where
    tspec = fst . typ



validateExpr :: (?spec::Spec, MonadError String me) => Scope -> Expr -> me ()
validateExpr s e = let ?scope = s 
                   in validateExpr' e

validateExpr' :: (?spec::Spec, ?scope::Scope, MonadError String me) => Expr -> me ()

-- * terms refer to variable or constants visible in the current scope
validateExpr' (ETerm _ n)        = do {checkTerm ?scope n; return ()}
validateExpr' (ELit _ _ _ _ _)   = return ()
validateExpr' (EBool _ _)        = return ()

-- * method application:
--   - method name refers to a visible method (local or exported)
--   - the number and types of arguments match
validateExpr' (EApply p mref as) = do
    (m, ScopeTemplate t) <- checkMethod ?scope mref
    assert (isJust $ methRettyp m) p $ "Method " ++ sname m ++ " has void return type and cannot be used in expression"
    assert ((length $ methArg m) == length as) p $
           "Method " ++ sname m ++ " takes " ++ show (length $ methArg m) ++ 
           " arguments, but is invoked with " ++ show (length as) ++ " arguments"
    mapM (\(marg,a) -> do validateExpr' a
                          assert (typeMatch marg a) (pos a) $
                                 "Argument type " ++ show (tspec a) ++ " does not match expected type " ++ show (tspec marg))
         (zip (map (ObjArg (ScopeMethod t m)) (methArg m)) as)
    return ()

-- * field selection refers to a valid struct field, or a valid and externally 
--   visible template variable, port or instance
validateExpr' (EField p e f) = do
    validateExpr' e
    case fst $ typ' e of
         StructSpec _ fs      -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
         TemplateTypeSpec _ t -> case objLookup (ObjTemplate (getTemplate t)) f of
                                      Nothing                -> err (pos f) $ "Unknown identifier " ++ show f
                                      Just (ObjPort   _ _)   -> return ()
                                      Just (ObjInstance _ _) -> return ()
                                      Just (ObjGVar   _ v)   -> assert (gvarExport v) (pos f) $
                                                                       "Cannot access private variable " ++ sname v ++ " of template " ++ show t
                                      _                      -> err (pos f) $ show f ++ " does not refer to an externally visible member of template " ++ show t
         _                    -> err (pos f) $ "Expression " ++ show e ++ " is not a struct or template"

validateExpr' (EPField p e f) = do
    validateExpr' e
    case typ' e of
         (PtrSpec _ t,s) -> case typ' (t,s) of
                                 (StructSpec _ fs, _) -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
                                 _                    -> err (pos f) $ "Expression " ++ show e ++ " is not a struct pointer"
         _                                            -> err (pos f) $ "Expression " ++ show e ++ " is not a pointer"


-- * index[]: applied to an array type expression; index value is a valid 
--   integral expression 
validateExpr' (EIndex _ a i) = do
    validateExpr' a
    validateExpr' i
    assert (isInt i) (pos i) $ show i ++ " is not of integral type"
    assert (isArray a) (pos i) $ show a ++ " is not an array"

validateExpr' (EUnOp p UMinus e) = do
    validateExpr' e
    assert (isInt e) p $ "Unary minus applied to expression " ++ show e ++ " of non-integral type"

validateExpr' (EUnOp p Not e) = do
    validateExpr' e
    assert (isBool e) p $ "Logical negation applied to expression " ++ show e ++ " of non-boolean type"

validateExpr' (EUnOp p BNeg e) = do
    validateExpr' e
    assert (isInt e) p $ "Bit-wise negation applied to expression " ++ show e ++ " of non-integral type"

validateExpr' (EUnOp p Deref e) = do
    validateExpr' e
    assert (isPtr e) p $ "Cannot dereference non-pointer expression " ++ show e

validateExpr' (EUnOp p AddrOf e) = do
    validateExpr' e
    assert (isLExpr ?scope e) p $ "Cannot take address of expression " ++ show e ++ ", which is not an L-value"

validateExpr' (EBinOp p op e1 e2) = do
    validateExpr' e1
    validateExpr' e2
    if elem op [Eq,Neq]
      then assert (typeComparable e1 e2) p $ "Operator " ++ show op ++ " applied to expressions " ++ show e1 ++ 
                                             " and " ++ show e2 ++ " that have uncomparable types"
      else return () 
    if elem op [Lt,Gt,Lte,Gte,BinMinus,BAnd,BOr,BXor,Mod,Mul]
       then do assert (isInt e1) p $ "First operand " ++ show e1 ++ " of " ++ show op ++ " is of non-integral type"
               assert (isInt e2) p $ "Second operand " ++ show e2 ++ " of " ++ show op ++ " is of non-integral type"
       else return ()
    if elem op [And,Or,Imp]
       then do assert (isBool e1) p $ "First operand " ++ show e1 ++ " of " ++ show op ++ " is of non-boolean type"
               assert (isBool e2) p $ "Second operand " ++ show e2 ++ " of " ++ show op ++ " is of non-boolean type"
       else return ()
    if elem op [BAnd, BOr, BXor]
       then assert (typeWidth e1 == typeWidth e2) p $ 
                   "Binary bitwise operator " ++ show op ++ " applied to arguments of different width: " ++
                   show e1 ++ " has width " ++ (show $ typeWidth e1) ++ ", " ++ 
                   show e2 ++ " has width " ++ (show $ typeWidth e2)
       else return ()

validateExpr' (ETernOp p e1 e2 e3) = do
    validateExpr' e1
    validateExpr' e2
    validateExpr' e3
    assert (isBool e1) (pos e1) $ "First operand " ++ show e1 ++ " of ?: is of non-boolean type"
    assert (typeMatch e1 e2) p $ "Arguments of ternary operator have incompatible types: " ++
                                 show e1 ++ " has type " ++ show (tspec e1) ++ ", " ++
                                 show e2 ++ " has type " ++ show (tspec e2)

-- * case: 
--    - case conditions must type-match the case expression (should they be statically computable?)
--    - value expressions and default expression must all have matching types
validateExpr' (ECase p e cs md) = do
    validateExpr' e
    mapM (\(e1,e2) -> do {validateExpr' e1; validateExpr' e2}) cs
    case md of
         Just d  -> validateExpr' d
         Nothing -> return ()
    mapM (\(e1,_) -> assert (typeComparable e e1) (pos e1) $ 
                     "Expression " ++ show e1 ++ " has type "  ++ (show $ tspec e1) ++ 
                     ", which does not match the type " ++ (show $ tspec e) ++ " of the key expression " ++ show e) cs
    case cs of
         []     -> return ()
         _      -> do let e1 = fst $ head cs
                      mapM (\(_,e2) -> assert (typeMatch e1 e2) (pos e2) $ 
                                              "Clauses of a case expression return values of incompatible types:\n  " ++ 
                                              show e1 ++ "(" ++ spos e1 ++ ") has type " ++ (show $ tspec e1) ++ "\n  " ++
                                              show e2 ++ "(" ++ spos e2 ++ ") has type " ++ (show $ tspec e2))
                           ((tail cs) ++ (map (undefined,) $ maybeToList md))
                      return ()
                      
-- * cond: 
--    - condition expressions are valid boolean expressions
--    - value expressions have compatible types
validateExpr' (ECond p cs md) = do
    mapM (\(e1,e2) -> do validateExpr' e1
                         validateExpr' e2
                         assert (isBool e1) (pos e1) $ "Expression " ++ show e1 ++ " is of non-boolean type")
         cs
    case md of
         Just d  -> validateExpr' d
         Nothing -> return ()
    case cs of
         []     -> return ()
         _      -> do let e1 = fst $ head cs
                      mapM (\(_,e2) -> assert (typeMatch e1 e2) (pos e2) $ 
                                              "Clauses of a conditional expression return values of incompatible types:\n  " ++ 
                                              show e1 ++ "(" ++ spos e1 ++ ") has type " ++ (show $ tspec e1) ++ "\n  " ++
                                              show e2 ++ "(" ++ spos e2 ++ ") has type " ++ (show $ tspec e2))
                           ((tail cs) ++ (map (undefined,) $ maybeToList md))
                      return ()
    
-- * slice: 
--    - applied to an integer (unsigned?) value; 
--    - lower and upper bounds are constant expressions
--    - 0 <= lower bound <= upper bound <= type width - 1
validateExpr' (ESlice p e (l,h)) = do
    validateExpr' e
    validateExpr' l
    validateExpr' h
    assert (isInt e) (pos e)                $ "Cannot compute slice of a non-integer expression " ++ show e
    assert (isConstExpr l) (pos l)          $ "Lower bound " ++ show l ++ " of a slice is a non-constant expression"
    assert (isConstExpr h) (pos h)          $ "Upper bound " ++ show h ++ " of a slice is a non-constant expression"
    assert (0 <= evalInt l) (pos l)         $ "Lower bound " ++ show l ++ " of a slice has negative value " ++ (show $ evalInt l)
    assert (evalInt l <= evalInt h) (pos l) $ "Lower bound " ++ show l ++ "=" ++ (show $ evalInt l) ++ " of a slice is greater than " ++
                                              "upper bound " ++ show h ++ "=" ++ (show $ evalInt h) 
    let w = typeWidth e
    assert (evalInt h < w) (pos l)          $ "Upper bound " ++ show h ++ "=" ++ (show $ evalInt h) ++ " of a slice " ++
                                              "exceeds argument width (" ++ show w ++ ") bits"

-- * struct:
--    - typename refers to a struct type
--    - correct number and types of fields
validateExpr' (EStruct p n es) = do
    (d,s) <- checkTypeDecl ?scope n
    let t = (tspec d,s)
    assert (isStruct t) (pos n) $ show n ++ " is not a struct type"
    let (StructSpec _ fs) = tspec d
        nes = case es of 
                   Left es -> length es
                   Right es -> length es
    assert (length fs = nes) p $ "struct " ++ name d ++ " has " ++ show (length fs) ++ " members, but "
    case es of
         Left  es -> mapM (\(n,e) -> ) es
         Right es ->


--fields::(Either [(Ident, Expr)] [Expr])} 

--ENonDet {epos::Pos}
