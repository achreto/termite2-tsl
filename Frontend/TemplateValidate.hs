{-# LANGUAGE FlexibleContexts, ImplicitParams, TupleSections, RecordWildCards #-}

module Frontend.TemplateValidate(checkConcreteTemplate,
                        validateTmInstances,
                        validateTmInstances2,
                        validateTmInit2,
                        validateTmPrefix2,
                        validateTmPorts,
                        validateTmDerives,
                        validateTmNS,
                        validateTmTypeDecls,
                        validateTmTypeDecls2,
                        validateTmConsts,
                        validateTmConsts2,
                        validateTmGVars,
                        validateTmGVars2,
                        validateTmWires,
                        validateTmWires2,
                        validateTmWires4,
                        validateTmMethods2,
                        validateTmProcesses2,
                        validateTmProcesses3,
                        validateTmGoals2,
                        validateTmRels2,
                        validateTmApply2) where

import Data.List
import Data.Maybe
import Data.Tuple.Select
import qualified Data.Map as M
import Control.Monad.Except
import Control.Applicative
import Debug.Trace

import TSLUtil
import Util hiding (name)
import Pos
import Name
import Frontend.Type
import Frontend.TypeOps
import Frontend.TypeValidate
import Frontend.Template
import Frontend.TemplateOps
import Frontend.TemplateFlatten
import Frontend.Spec
import Frontend.ConstOps
import Frontend.TVar
import Frontend.TVarOps
import Frontend.TVarValidate
import Frontend.ExprOps
import Frontend.ExprValidate
import Frontend.Method
import Frontend.MethodOps
import Frontend.MethodValidate
import Frontend.Process
import Frontend.ProcessOps
import Frontend.StatementOps
import Frontend.StatementValidate
import Frontend.Relation
import Frontend.RelationValidate
import Frontend.NS

checkConcreteTemplate :: (?spec::Spec, MonadError String me) => Template -> Pos -> me ()
checkConcreteTemplate t p = do
    let (purem, purew) = tmPure t
    assert (null purem) p $
           "Cannot instantiate pure template " ++ sname t ++ ". The following methods are not implemented: " ++ 
           (intercalate ", " $ map sname purem)
    assert (null purew) p $
           "Cannot instantiate pure template " ++ sname t ++ ". The following wires are not assigned: " ++ 
           (intercalate ", " $ map sname purew)


-----------------------------------------------------------
-- Validate template instances
-- * Every instance refers to a valid template and takes
--   correct number and types of arguments
-- Second pass: 
-- * only concrete templates can be instantiated
-----------------------------------------------------------

-- Validate template instantiation statement
-- * template name is valid
-- * correct number and types of parameters
validateInstance :: (?spec::Spec, MonadError String me) => Template -> Instance -> me ()
validateInstance tm i = do
    checkTemplate $ instTemplate i
    let t = getTemplate $ instTemplate i
    assert ((length $ tmPort t) == (length $ instPort i)) (pos i) $ 
           "Incorrect number of parameters to template " ++ sname t ++ 
           ". " ++ (show $ length $ tmPort t) ++ " parameters required."
    mapM (\(p,n) -> do ptm <- tmLookupPortInst tm n
                       let parents = ptm : (map name $ tmParentsRec $ getTemplate ptm)
                       assert (elem (portTemplate p) parents) (pos n) $ 
                              "Invalid template parameter: expected template type: " ++ (show $ portTemplate p) ++ ", actual type: " ++ show ptm)
         (zip (tmPort t) (instPort i))
    return ()


validateTmInstances :: (?spec::Spec,MonadError String me) => Template -> me ()
validateTmInstances tm = do {mapM (validateInstance tm) (tmInst tm); return()}

validateInstance2 :: (?spec::Spec, MonadError String me) => Template -> Instance -> me ()
validateInstance2 tm i = 
    checkConcreteTemplate (getTemplate $ instTemplate i) (pos i)

validateTmInstances2 :: (?spec::Spec,MonadError String me) => Template -> me ()
validateTmInstances2 tm = do {mapM (validateInstance2 tm) (tmInst tm); return()}

-----------------------------------------------------------
-- Validate template port
-- * port refers to a valid template 
-----------------------------------------------------------

validatePort :: (?spec::Spec, MonadError String me) => Template -> Port -> me ()
validatePort tm p = do {checkTemplate $ portTemplate p; return ()}

validateTmPorts :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmPorts tm = do {mapM (validatePort tm) (tmPort tm); return()}


-----------------------------------------------------------
-- Validate template derivation
-----------------------------------------------------------

validateDerive :: (?spec::Spec, MonadError String me) => Template -> Derive -> me ()
validateDerive tm d = do
    checkTemplate $ drvTemplate d
    let t = getTemplate $ drvTemplate d
    mapM (\p -> do case find ((== name p) . name) (tmPort tm) of
                        Nothing -> err (pos d) $ "Template " ++ sname t ++ " expects port " ++ sname p ++ 
                                                 ", but no such port is defined in template " ++ sname tm
                        Just p' -> assert (isDescendant (getTemplate $ portTemplate p) (getTemplate $ portTemplate p')) (pos d) $
                                          "Local port " ++ sname p' ++ " has type " ++ (show $ portTemplate p') ++ 
                                          ", but parent template " ++ sname t ++ " expects this port to be of type " ++ (show $ portTemplate p))
         (tmPort t)
    return ()

validateTmDerives :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmDerives tm = do {mapM (validateDerive tm) (tmDerive tm); return()}

------------------------------------------------------------------------------
-- Validate prefix blocks
------------------------------------------------------------------------------

validatePrefix2 :: (?spec::Spec, MonadError String me) => Template -> Prefix -> me ()
validatePrefix2 t a = do
    let ?scope = ScopeTemplate t
        ?privoverride = False
    validateStat' False (prefBody a)

validateTmPrefix2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmPrefix2 t = do {mapM (validatePrefix2 t) (tmPrefix t); return ()}

------------------------------------------------------------------------------
-- Validate init blocks 
------------------------------------------------------------------------------

validateInit2 :: (?spec::Spec, MonadError String me) => Template -> Init -> me ()
validateInit2 t i = do
    let ?scope = ScopeTemplate t
        ?privoverride = False
    validateExpr' (initBody i)
    assert (exprNoSideEffects $ initBody i) (pos $ initBody i) "Initial conditions must be side-effect free"

validateTmInit2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmInit2 t = do {mapM (validateInit2 t) (tmInit t); return ()}


------------------------------------------------------------------------------
-- Validate goals at the second pass
------------------------------------------------------------------------------

validateGoal2 :: (?spec::Spec, MonadError String me) => Template -> Goal -> me ()
validateGoal2 t g = do
    let ?scope = ScopeTemplate t
        ?privoverride = False
    validateExpr' (goalCond g)
    assert (exprNoSideEffects $ goalCond g) (pos $ goalCond g) "Goal conditions must be side-effect free"
    assert (isBool $ exprType $ goalCond g) (pos $ goalCond g) $ "Goal must be a boolean expression"

validateTmGoals2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmGoals2 t = do {mapM (validateGoal2 t) (tmGoal t); return ()}

------------------------------------------------------------------------------
-- Validate type decls
------------------------------------------------------------------------------
validateTmTypeDecls :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmTypeDecls tm = do {mapM (validateTypeSpec (ScopeTemplate tm) . tspec) (tmTypeDecl tm); return()}

validateTmTypeDecls2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmTypeDecls2 tm = do {mapM (validateTypeSpec2 (ScopeTemplate tm) . tspec) (tmTypeDecl tm); return()}

------------------------------------------------------------------------------
-- Validate constant declarations
------------------------------------------------------------------------------

validateTmConsts :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmConsts tm = do {mapM (validateConst (ScopeTemplate tm)) (tmConst tm); return()}

validateTmConsts2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmConsts2 tm = do {mapM (validateConst2 (ScopeTemplate tm)) (tmConst tm); return()}


------------------------------------------------------------------------------
-- Validate global variables
-- * First pass: validate type specs
-- * Second pass: validate initial assignment expressions; check that 
--   continuous assignment variables do not have initial assignments
------------------------------------------------------------------------------

validateGVar2 :: (?spec::Spec, MonadError String me) => Template -> GVar -> me ()
validateGVar2 tm v = do let ?scope = ScopeTemplate tm
                        validateVar2 ?scope (gvarVar v)
                        case (varInit $ gvarVar v) of
                             Nothing -> return ()
                             Just e  -> assert (isConstExpr e) (pos e) $ "Initial value of a global variable must be a constant expression"

validateTmGVars :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmGVars tm = do {mapM (validateVar (ScopeTemplate tm) . gvarVar) (tmVar tm); return()}

validateTmGVars2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmGVars2 tm = do {mapM (validateGVar2 tm) (tmVar tm); return()}

------------------------------------------------------------------------------
-- Validate continuous assignments:
-- First pass:
-- * LHS must be a global variable
-- * LHSs must be unique
-- Second pass:
-- * RHS is a valid expressions of matching type
-- * no circular dependencies between continuous assignments
------------------------------------------------------------------------------

-- Find declaration of the wire inherited from a parent
wireParent :: (?spec::Spec) => Template -> Wire -> Maybe (Template, Wire)
wireParent t w = 
    case listToMaybe $ catMaybes $ map (\t' -> objLookup (ObjTemplate t') (name w)) (tmParents t) of
         Nothing                -> Nothing
         Just (ObjWire t' w')   -> Just (t',w')

-- Check if the wire overrides a derived declaration and, if so, 
-- make sure that its type matches previous declaration
validateWire :: (?spec::Spec, MonadError String me) => Template -> Wire -> me ()
validateWire t w = do
   case wireParent t w of
        Nothing      -> validateTypeSpec (ScopeTemplate t) (tspec w)
        Just (_,w')  -> assert (tspec w' == tspec w) (pos w) $ 
                               "Wire " ++ sname w ++ " was declared with type " ++ (show $ tspec w') ++ " at " ++ spos w' ++
                               " but s redefined as " ++ (show $ tspec w) ++ " at " ++ spos w

validateTmWires :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmWires t = do {mapM (validateWire t) (tmWire t); return ()}

validateWire2 :: (?spec::Spec, MonadError String me) => Template -> Wire -> me () 
validateWire2 t w = do
    let ?scope = ScopeTemplate t
        ?privoverride = False
    case wireRHS w of
         Just e  -> do validateExpr' e
                       checkTypeMatch e (Type ?scope $ tspec w) (exprType e)
                       assert (exprNoSideEffects e) (pos e) "Wire expression must be side-effect free"
         Nothing -> return ()

validateTmWires2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmWires2 t = do {mapM (validateWire2 t) (tmWire t); return ()}

validateTmWires4 :: (?spec::Spec, MonadError String me) => me ()
validateTmWires4 = 
    case grCycle $ wireGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Cyclic wire dependency: " ++ (intercalate "->" $ map (show . snd) c) 

------------------------------------------------------------------------------
-- Validate method declarations (only safe during the second pass)
------------------------------------------------------------------------------

validateTmMethods2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmMethods2 tm = do {mapM (validateMeth tm) (tmMethod tm); return ()}

------------------------------------------------------------------------------
-- Validate process declarations (only safe during the second pass)
------------------------------------------------------------------------------

validateTmProcesses2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmProcesses2 tm = do {mapM (validateProc tm) (tmProcess tm); return ()}

-- Third pass (after the template has been merged with its parents)
validateTmProcesses3 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmProcesses3 tm = uniqNames (\n -> "Process " ++ n ++ " declared multiple times in template " ++ sname tm) 
                                    (map sel1 $ tmSubprocess tm)

------------------------------------------------------------------------------
-- Validate relation and apply declarations
------------------------------------------------------------------------------

validateTmRels2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmRels2 tm = do {mapM (validateRelation tm) (tmRelation tm); return ()}

validateTmApply2 :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmApply2 tm = do {mapM (\Apply{..} -> validateApply (ScopeTemplate tm) applyRel applyArg) (tmApply tm); return ()}

------------------------------------------------------------------------------
-- Validate template namespace
-- 1. No identifier is declared twice in a template
-- 2. Template-level declarations don't conflict with specification-level
--    declarations
-- 2. Template does not derive the same identifier from multiple parents
------------------------------------------------------------------------------

-- * No identifier is declared twice in a template
-- * Template-level declarations don't conflict with specification-level
--   declarations
-- * No illegal overrides
validateTmNS :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmNS t = do
    let ns = tmLocalDecls t
    uniqNames (\n -> "Identifier " ++ n ++ " declared multiple times in template " ++ sname t) ns
    case mapMaybe (\o -> fmap (o,) $ find (\o' -> name o' == name o) specNamespace) ns of
         []       -> return ()
         (o,o'):_ -> err (pos o) $ "Identifier " ++ sname o ++ " conflicts with global declaration at " ++ spos o'
    checkTmOverrides t
    validateTmDeriveNS t


-- * derived template-level namespaces do not overlap
validateTmDeriveNS :: (?spec::Spec, MonadError String me) => Template -> me ()
validateTmDeriveNS t = do
    let nss = map (\d -> map (d,) $ tmLocalAndParentDecls $ getTemplate $ drvTemplate d) (tmDerive t)
    foldM (\names ns -> case intersectBy (\o1 o2 -> (name $ snd o1) == (name $ snd o2)) names ns of
                             []      -> return $ names++ns
                             (d,o):_ -> err (pos d) $ "Template " ++ sname t ++ " derives mutiple declarations of identifier " ++ sname o ++ 
                                                      " from the following templates: " ++ 
                                                      (intercalate ", " $ map (show . drvTemplate . fst) $ filter ((==name o) . name . snd) (names++ns)))
          [] nss
    return ()

-- * only methods, wires and ports can be overloaded
checkTmOverrides :: (?spec::Spec, MonadError String me) => Template -> me ()
checkTmOverrides t = do
    let local = tmLocalDecls t
        enviro = specNamespace ++ (concat $ map (tmLocalAndParentDecls . getTemplate . drvTemplate) (tmDerive t))
        override = filter (\(o1,o2) -> name o1 == name o2) $ (,) <$> local <*> enviro
    mapM (\(o1,o2) -> case (o1,o2) of
                           (ObjMethod _ m1, ObjMethod _ m2) -> return ()
                           (ObjPort _ p1,   ObjPort _ p2)   -> return ()
                           (ObjWire _ w1,   ObjWire _ w2)   -> return ()
                           _                                -> err (pos o1) $ "Identifier " ++ (sname o1) ++ " overrides previous declaration at " ++ spos o2)
         override
    return ()
