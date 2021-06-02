{-# LANGUAGE ImplicitParams, TupleSections, FlexibleContexts, RecordWildCards #-}

module Frontend.ExprValidate(validateExpr, validateExpr', validateRegExpr',
                             validateCall, validateApply) where

import Control.Monad.Except
import Data.Maybe

import Util hiding (name)
import TSLUtil
import Pos
import Name
import Frontend.Type
import Frontend.TypeOps
import Frontend.NS
import Frontend.Expr
import Frontend.ExprOps
import Frontend.Method
import Frontend.Spec
import Frontend.Template
import Frontend.TemplateOps
import Frontend.Relation
import Frontend.RelationOps

validateRegExpr' :: (?spec::Spec, ?scope::Scope, ?privoverride::Bool, MonadError String me) => Expr -> me ()
validateRegExpr' e = do
    validateExpr' e
    assert (not $ any isObjTxOutput $ exprObjs e) (pos e) $ "Illegal read access to transducer output port"
    assert (not $ any isObjTxInput $ exprObjs e) (pos e) $ "Illegal read access to transducer input port"


validateExpr :: (?spec::Spec, ?privoverride::Bool, MonadError String me) => Scope -> Expr -> me ()
validateExpr s e = let ?scope = s 
                   in validateExpr' e

validateExpr' :: (?spec::Spec, ?scope::Scope, ?privoverride::Bool, MonadError String me) => Expr -> me ()

-- * terms refer to variable or constants visible in the current scope
validateExpr' (ETerm _ n)        = do {_ <- checkTerm ?scope n; return ()}
validateExpr' (ELit _ _ _ _ _)   = return ()
validateExpr' (EBool _ _)        = return ()
validateExpr' (EAtLab p lab)     = do 
    assert (?scope /= ScopeTop) p $ "Label used outside template scope"
    assert (elem lab $ tmLabels (scopeTm ?scope)) p $ "Unknown label " ++ show lab

-- * method application:
--   - method name refers to a visible method (local or exported)
--   - the number and types of arguments match
validateExpr' (EApply p mref as) = do
    validateCall p mref as
    let (_, m) = getMethod ?scope mref
    assert (isJust $ methRettyp m) p $ "Method " ++ sname m ++ " has void return type and cannot be used in expression"

-- * field selection refers to a valid struct field, or a valid and externally 
--   visible template variable, port or instance
validateExpr' (EField _ e f) = do
    validateExpr' e
    case tspec $ typ' $ exprType e of
         StructSpec _ fs      -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
         TemplateTypeSpec _ t -> case objLookup (ObjTemplate (getTemplate t)) f of
                                      Nothing                -> err (pos f) $ "Unknown identifier " ++ show f
                                      Just (ObjPort   _ _)   -> return ()
                                      Just (ObjInstance _ _) -> return ()
                                      Just (ObjGVar   _ v)   -> assert (gvarExport v || ?privoverride) (pos f) $
                                                                       "Cannot access private variable " ++ sname v ++ " of template " ++ show t
                                      Just (ObjWire   _ w)   -> assert (wireExport w || ?privoverride) (pos f) $
                                                                       "Cannot access private wire " ++ sname w ++ " of template " ++ show t
                                      _                      -> err (pos f) $ show f ++ " does not refer to an externally visible member of template " ++ show t
         _                    -> err (pos f) $ "Expression " ++ show e ++ " is not a struct or template"

validateExpr' (EPField _ e f) = do
    validateExpr' e
    case typ' $ exprType e of
         (Type s (PtrSpec _ t)) -> case tspec $ typ' $ Type s t of
                                        StructSpec _ fs -> assert (any ((==f) . name) fs) (pos f) $ "Unknown field name " ++ show f
                                        _               -> err (pos f) $ "Expression " ++ show e ++ " is not a struct pointer"
         _                      -> err (pos f) $ "Expression " ++ show e ++ " is not a pointer"


-- * index[]: applied to an array type expression; index value is a valid 
--   integral expression 
validateExpr' (EIndex _ a i) = do
    validateExpr' a
    validateExpr' i
    assert (isInt $ exprType i) (pos i) $ show i ++ " is not of integral type"
    assert (isArray $ exprType a) (pos i) $ show a ++ " is not an array"

validateExpr' (ERange _ a (fi,l)) = do
    validateExpr' a
    validateExpr' fi
    validateExpr' l
    assert (isInt $ exprType fi)  (pos fi) $ show fi ++ " is not of integral type"
    assert (isInt $ exprType l)   (pos l)  $ show l  ++ " is not of integral type"
    assert (isArray $ exprType a) (pos a)  $ show a  ++ " is not an array"

validateExpr' (ELength _ a) = do
    validateExpr' a
    assert (isArray $ exprType a) (pos a) $ show a ++ " is not an array"

validateExpr' (EUnOp p UMinus e) = do
    validateExpr' e
    assert (isInt $ exprType e) p $ "Unary minus applied to expression " ++ show e ++ " of non-integral type"

validateExpr' (EUnOp p Not e) = do
    validateExpr' e
    assert (isBool $ exprType e) p $ "Logical negation applied to expression " ++ show e ++ " of non-boolean type"

validateExpr' (EUnOp p BNeg e) = do
    validateExpr' e
    assert (isInt $ exprType e) p $ "Bit-wise negation applied to expression " ++ show e ++ " of non-integral type"

validateExpr' (EUnOp p Deref e) = do
    assert (not $ isTemplateScope ?scope) p "Pointer dereference inside always-block"
    validateExpr' e
    assert (isPtr $ exprType e) p $ "Cannot dereference non-pointer expression " ++ show e

validateExpr' (EUnOp p AddrOf e) = do
    validateExpr' e
    assert (isMemExpr e) p $ "Cannot take address of expression " ++ show e

validateExpr' (EBinOp p op e1 e2) = do
    validateExpr' e1
    validateExpr' e2
    if elem op [Eq,Neq]
      then assert (typeComparable (exprType e1) (exprType e2)) p $ "Operator " ++ show op ++ " applied to expressions " ++ show e1 ++ 
                                                                   " and " ++ show e2 ++ " that have uncomparable types " ++ (showType $ exprType e1) ++ " and " ++ (showType $ exprType e2)
      else return () 
    if elem op [Lt,Gt,Lte,Gte,BinMinus,BAnd,BOr,BXor,BConcat,Mod,Mul]
       then do assert (isInt $ exprType e1) p $ "First operand " ++ show e1 ++ " of " ++ show op ++ " is of non-integral type"
               assert (isInt $ exprType e2) p $ "Second operand " ++ show e2 ++ " of " ++ show op ++ " is of non-integral type"
       else return ()
    if elem op [And,Or,Imp]
       then do assert (isBool $ exprType e1) p $ "First operand " ++ show e1 ++ " of " ++ show op ++ " is of non-boolean type"
               assert (isBool $ exprType e2) p $ "Second operand " ++ show e2 ++ " of " ++ show op ++ " is of non-boolean type"
       else return ()
    if elem op [BAnd, BOr, BXor]
       then assert (exprWidth e1 == exprWidth e2) p $ 
                   "Binary bitwise operator " ++ show op ++ " applied to arguments of different width: " ++
                   show e1 ++ " has width " ++ (show $ exprWidth e1) ++ ", " ++ 
                   show e2 ++ " has width " ++ (show $ exprWidth e2)
       else return ()

validateExpr' (ETernOp p e1 e2 e3) = do
    validateExpr' e1
    validateExpr' e2
    validateExpr' e3
    assert (isBool $ exprType e1) (pos e1) $ "if condition " ++ show e1 ++ " is of non-boolean type"
    assert (typeMatch (exprType e2) (exprType e3)) p $ "Arguments of ternary operator have incompatible types: " ++
                                                       show e1 ++ " has type " ++ show (exprTypeSpec e1) ++ ", " ++
                                                       show e2 ++ " has type " ++ show (exprTypeSpec e2)

-- * case: 
--    - case conditions must type-match the case expression (should they be statically computable?)
--    - value expressions and default expression must all have matching types
validateExpr' (ECase p e cs md) = do
    validateExpr' e
    assert (length cs > 0) p $ "Empty case expression"
    _ <- mapM (\(e1,e2) -> do validateExpr' e1
                              validateExpr' e2
                              assert (exprNoSideEffects e1) (pos e1) "Case label must be side-effect free")
         cs
    case md of
         Just d  -> validateExpr' d
         Nothing -> return ()
    _ <- mapM (\(e1,_) -> assert (typeComparable (exprType e) (exprType e1)) (pos e1) $ 
                          "Expression " ++ show e1 ++ " has type "  ++ (show $ exprTypeSpec e1) ++ 
                          ", which does not match the type " ++ (show $ exprTypeSpec e) ++ " of the key expression " ++ show e) cs
    let e1 = snd $ head cs
    _ <- mapM (\(_,e2) -> assert (typeMatch (exprType e1) (exprType e2)) (pos e2) $ 
                                 "Clauses of a case expression return values of incompatible types:\n  " ++ 
                                 show e1 ++ "(" ++ spos e1 ++ ") has type " ++ (show $ exprTypeSpec e1) ++ "\n  " ++
                                 show e2 ++ "(" ++ spos e2 ++ ") has type " ++ (show $ exprTypeSpec e2))
              ((tail cs) ++ (map (undefined,) $ maybeToList md))
    return ()
                      
-- * cond: 
--    - condition expressions are valid boolean expressions
--    - value expressions have compatible types
validateExpr' (ECond p cs md) = do
    assert (length cs > 0) p "Empty case expression"
    _ <- mapM (\(e1,e2) -> do validateExpr' e1
                              validateExpr' e2
                              assert (exprNoSideEffects e1) (pos e1) "Condition must be side-effect free"
                              assert (isBool $ exprType e1) (pos e1) $ "Expression " ++ show e1 ++ " is of non-boolean type")
         cs
    case md of
         Just d  -> validateExpr' d
         Nothing -> return ()
    let e1 = snd $ head cs
    _ <- mapM (\(_,e2) -> assert (typeMatch (exprType e1) (exprType e2)) (pos e2) $ 
                                 "Clauses of a conditional expression return values of incompatible types:\n  " ++ 
                                 show e1 ++ "(" ++ spos e1 ++ ") has type " ++ (show $ exprTypeSpec e1) ++ "\n  " ++
                                 show e2 ++ "(" ++ spos e2 ++ ") has type " ++ (show $ exprTypeSpec e2))
              ((tail cs) ++ (map (undefined,) $ maybeToList md))
    return ()
    
-- * slice: 
--    - applied to an integer (unsigned?) value; 
--    - lower and upper bounds are constant expressions
--    - 0 <= lower bound <= upper bound <= type width - 1
validateExpr' (ESlice _ e (l,h)) = do
    validateExpr' e
    validateExpr' l
    validateExpr' h
    assert (isInt $ exprType e) (pos e)     $ "Cannot compute slice of a non-integer expression " ++ show e
    assert (isConstExpr l) (pos l)          $ "Lower bound " ++ show l ++ " of a slice is a non-constant expression"
    assert (isConstExpr h) (pos h)          $ "Upper bound " ++ show h ++ " of a slice is a non-constant expression"
    assert (0 <= evalInt l) (pos l)         $ "Lower bound " ++ show l ++ " of a slice has negative value " ++ (show $ evalInt l)
    assert (evalInt l <= evalInt h) (pos l) $ "Lower bound " ++ show l ++ "=" ++ (show $ evalInt l) ++ " of a slice is greater than " ++
                                              "upper bound " ++ show h ++ "=" ++ (show $ evalInt h) 
    let w = exprWidth e
    assert (evalInt h < fromIntegral w) (pos h) $ "Upper bound " ++ show h ++ "=" ++ (show $ evalInt h) ++ " of a slice " ++
                                                  "exceeds argument width (" ++ show w ++ ") bits"

-- * struct:
--    - typename refers to a struct type
--    - correct number and types of fields
validateExpr' (EStruct p tn mes) = do
    (d,s) <- checkTypeDecl ?scope tn
    let t = Type s $ tspec d
    assert (isStruct t) (pos tn) $ show tn ++ " is not a struct type"
    let (StructSpec _ fs) = tspec $ typ' t
        nes = case mes of 
                   Left es -> length es
                   Right es -> length es
    assert (length fs == nes) p $ "struct " ++ sname d ++ " has " ++ show (length fs) ++ " members, but is instantiated with " ++  show nes ++ " members"
    _ <- case mes of
              Left  es -> mapIdxM (\((n,e),f) i -> do assert (n == name f) (pos n) $ 
                                                          "Incorrect field name: field " ++ show i ++ " of struct " ++ sname d ++ " has name " ++ show n
                                                      validateExpr' e
                                                      assert (typeComparable (exprType e) (Type s $ tspec f)) (pos e) $ 
                                                           "Could not match expected type " ++ (show $ tspec f) ++ " with actual type " ++ (show $ exprTypeSpec e) ++ " in expression " ++ show e)
                                  $ zip es fs
              Right es -> mapM (\(e,f) -> do validateExpr' e
                                             assert (typeComparable (exprType e) $ Type s $ tspec f) (pos e) $ 
                                                 "Could not match expected type " ++ (show $ tspec f) ++ " with actual type " ++ (show $ exprTypeSpec e) ++ " in expression " ++ show e)
                                  $ zip es fs
    return ()

validateExpr' (ERel p n as) = 
    case ?scope of
         ScopeTop -> err p "relation instantiation in top-level scope"
         _        -> validateApply ?scope n as

validateExpr' (ENonDet p _) = 
    case ?scope of
         ScopeMethod  _ m -> case methCat m of
                                  Function            -> err p "non-deterministic value inside function"
                                  Procedure           -> err p "non-deterministic value inside procedure"
                                  Task Uncontrollable -> err p "non-deterministic value inside uncontrollable task"
                                  _                   -> return ()
         ScopeProcess _ _  -> return ()
         ScopeTemplate _   -> err p "non-deterministic value inside always-block"


-- Common code to validate method calls in statement and expression contexts
validateCall :: (?spec::Spec, ?scope::Scope, ?privoverride::Bool, MonadError String me) => Pos -> MethodRef -> [Maybe Expr] -> me ()
validateCall p mref as = do
    let isfunc = isFunctionScope ?scope
        istm   = isTemplateScope ?scope
    (t,m) <- checkMethod ?scope mref
    assert ((length $ methArg m) == length as) p $
           "Method " ++ sname m ++ " takes " ++ show (length $ methArg m) ++ 
           " arguments, but is invoked with " ++ show (length as) ++ " arguments"
    assert ((not isfunc) || (methCat m == Function)) (pos mref) $ show (methCat m) ++ " invocation not allowed in function context"
    assert ((not istm) || (elem (methCat m) [Function,Procedure])) (pos mref) $ show (methCat m) ++ " invocation not allowed in template context"
    _ <- mapM (\(marg,ma) -> case ma of
                                  Nothing -> assert (argDir marg == ArgOut) p $ "Input argument " ++ sname marg ++ " is not specified in invocation of method " ++ sname m
                                  Just a  -> do validateExpr' a
                                                checkTypeMatch a (objType $ ObjArg (ScopeMethod t m) marg) (exprType a)
                                                assert ((not isfunc) || exprNoSideEffects a) (pos a) $ "Expression " ++ show a ++ " has side effects"
                                                when (argDir marg == ArgOut) $
                                                    do assert (isLExpr a) (pos a) $ "Expression " ++ show a ++ " is not an L-value"
                                                       assert ((not isfunc) || (isLocalLHS a)) (pos a) $ "out argument " ++ sname marg ++ " of method " ++ sname m ++ " refers to non-local state")
              (zip (methArg m) as)
    return ()

validateApply :: (?spec::Spec, MonadError String me) => Scope -> Ident -> [Expr] -> me ()
validateApply sc rel args = trace ("validateApply " ++ show sc ++ " " ++ show rel) $ do
    let ?privoverride = False
    -- Relation name refers to a valid relation
    (_, r@Relation{..}) <- checkRelation sc rel
    -- Argument list has correct length
    assert (length args == length relArg) (pos rel) $ "Relation " ++ sname r ++ " is defined with " ++ show (length relArg) ++ 
                                                      " arguments, but is instantiated with " ++ show (length args) ++ " arguments" 
    -- Relation arguments are 
    -- * valid expressions
    -- * of matching types
    _ <- mapM (\(aa, ra) -> do validateExpr sc aa
                               let ?scope = sc
                               checkTypeMatch ra (exprType aa) (rargType ra))
         $ zip args relArg
    return ()

