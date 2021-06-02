{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.SpecOps(specNamespace,
               validateSpec,
               flatten) where

import Data.List
import Data.Maybe
import Control.Monad.Except
import Debug.Trace

import TSLUtil
import Frontend.Type
import Frontend.TypeOps
import Frontend.TypeValidate
import Pos
import Name
import Frontend.Spec
import Frontend.SpecInline
import Frontend.NS
import Frontend.Method
import Frontend.Template
import Frontend.TemplateOps
import Frontend.Transducer
import Frontend.TransducerValidate
import Frontend.TemplateValidate
import Frontend.InstTree
import Frontend.TemplateFlatten
import Frontend.Const
import Frontend.ConstOps
import Frontend.Expr
import Frontend.ExprOps
import Frontend.ExprFlatten
import Frontend.StatementOps

-- TODO:
--
-- Checks that require CFG analysis
-- * All exits from non-void methods end with a return statement
--
-- Checks to be performed on pre-processed spec
-- * variable visibility violations:
--   - variables automatically tainted as invisible because they are accessed from invisible context 
--     (process or invisible task) cannot be read inside uncontrollable visible transitions (which
--     correspond to executable driver code)


-----------------------------------------------------------------------------
-- Validation
-----------------------------------------------------------------------------

-- Main validation function
--
-- Validation order:
--
-- First pass:
-- * Validate top-level namespace
-- * Validate template instances (required by derive statements)
-- * Validate template ports (required by derive statements)
-- * Validate derive statements (required to build template namespaces)
-- * Validate template namespaces
-- * Validate type decls (but not array sizes)
-- * Validate constant types (but not initial assignments)
-- * Validate global variable types (but not initial assignments)
-- * Validate continuous assignments (LHS only)
--
-- Second pass: We are now ready to validate components of the specification containing expressions:
-- * Validate method declarations and implementation
-- * Validate template instances (only concrete templates can be instantiated, no circular instantiations)
-- * Validate processes
-- * Validate initial assignment expressions in constant declarations
-- * Validate array size declarations (must be integer constants)
-- * Validate initial variable assignments
-- * Validate prefix-blocks
-- * Validate RHS of wire assignments
-- * Validate goals
-- * Validate call graph

validateSpec :: (MonadError String me) => Spec -> me ()
validateSpec s = do
    let ?spec = s
    -- First pass
    validateSpecNS
    mapM validateTmPorts                      (specTemplate s)
    mapM validateTmDerives                    (specTemplate s)
    mapM validateTmInstances                  (specTemplate s)
    validateSpecDerives
    mapM validateTmNS                         (specTemplate s)
    mapM validateTxNS                         (specTransducer s)
    mapM (validateTypeSpec ScopeTop . tspec)  (specType s)
    mapM validateTmTypeDecls                  (specTemplate s)
    validateTypeDeps
    mapM (validateConst ScopeTop)             (specConst s)
    mapM validateTmConsts                     (specTemplate s)
    mapM validateTmGVars                      (specTemplate s)
    mapM validateTmWires                      (specTemplate s)

    -- Second pass
    mapM validateTmInit2                      (specTemplate s)
    mapM validateTmPrefix2                    (specTemplate s)
    mapM validateTmMethods2                   (specTemplate s)
    mapM validateTxImplementation2            (specTransducer s)
    mapM validateTmInstances2                 (specTemplate s)
    validateSpecInstances2
    mapM validateTmProcesses2                 (specTemplate s)
    mapM (validateConst2 ScopeTop)            (specConst s)
    mapM validateTmConsts2                    (specTemplate s)
    mapM validateTmGVars2                     (specTemplate s)
    mapM (validateTypeSpec2 ScopeTop . tspec) (specType s)
    mapM validateTmTypeDecls2                 (specTemplate s)
    mapM validateTmWires2                     (specTemplate s)
    mapM validateTmGoals2                     (specTemplate s)
    mapM validateTmRels2                      (specTemplate s)
    mapM validateTmApply2                     (specTemplate s)

    return ()

-- Validate top-level namespace:
-- * No identifier is declared twice at the top level
validateSpecNS :: (?spec::Spec, MonadError String me) => me ()
validateSpecNS = 
    uniqNames (\n -> "Identifier " ++ n ++ " declared more than once in the top-level scope") specNamespace

-- Validate the derivation graph of a spec
-- * no circular derivations
validateSpecDerives :: (?spec::Spec, MonadError String me) => me ()
validateSpecDerives = 
    case grCycle $ fst drvGraph of
         Nothing -> return ()
         Just c  -> err (pos $ snd $ head c) $ "Template derivation cycle: " ++ (intercalate "->" $ map (show . snd) c) 

-- Validate the instantiation graph of a spec
-- * no circular derivations
validateSpecInstances2 :: (?spec::Spec, MonadError String me) => me ()
validateSpecInstances2 = case grCycle instGraph of
                              Nothing -> return ()
                              Just c  -> err (pos $ snd $ head c) $ "Template instantiation cycle: " ++ (intercalate "->" $ map (show . snd) c) 

-- Validate the callgraph of the spec
-- * no recursion
-- * task invocations occur in legal scopes
validateSpecCallGraph2 :: (?spec::Spec, MonadError String me) => me ()
validateSpecCallGraph2 = do
    case grCycle callGraph of
         Nothing -> return ()
         Just c  -> err p $ "Recursive method invocation: " ++ 
                            (intercalate "->" $ map (\(_, s) -> 
                                   case s of
                                        ScopeMethod  t m -> sname t ++ "::" ++ sname m
                                        ScopeProcess t p -> sname t ++ "::" ++ sname p) c)
                    where p = case snd $ head c of
                                   ScopeMethod _ m  -> pos m
                                   ScopeProcess _ p -> pos p
    mapM (\t -> mapM (\s -> mapM (\s' -> checkCall s s') (callees s)) 
                     (tmScopes t))
         (filter isConcreteTemplate $ specTemplate ?spec)
    return ()

checkCall :: (?spec::Spec, MonadError String me) => Scope -> (Pos, (Template, Method)) -> me ()
checkCall (ScopeProcess _ pr) (p, (t,m)) = 
    assert (methCat m /= Task Controllable) p $ "Controllable task invoked in process context"
checkCall (ScopeMethod _ m1) (p, (t,m2)) = do
    let c1 = methCat m1
        c2 = methCat m2
    assert (not $ c1 == Task Controllable && c2 == Task Controllable) p   $ "Controllable task invoked in controllable task context"
    assert (not $ c1 == Task Controllable && c2 == Task Uncontrollable) p $ "Uncontrollable task invoked in controllable task context"
    assert (not $ c1 == Task Uncontrollable && c2 == Task Invisible) p    $ "Invisible task invoked in uncontrollable task context"
    assert (not $ c1 == Task Invisible && c2 == Task Controllable) p      $ "Controllable task invoked in invisible task context"

-- Map function over all expressions in the spec
specMapExpr :: (Scope -> Expr -> Expr) -> Spec -> Spec
specMapExpr f s =
    let ?spec = s
    in let tm' = map (tmMapExpr f) (specTemplate s)
           t'  = map (\t -> TypeDecl (pos t) (tspecMapExpr f ScopeTop $ tspec t) (name t)) (specType s)
           c'  = map (\c -> c{constVal = mapExpr f ScopeTop (constVal c)}) (specConst s)
           tx' = map (\t -> t{txBody = case txBody t of
                                            Left is  -> Left is
                                            Right s  -> Right $ statMapExpr f (ScopeTransducer t) s}) (specTransducer s)
       in Spec tm' t' c' tx'

-- Map function over all TypeSpec's in the spec
specMapTSpec :: (Scope -> TypeSpec -> TypeSpec) -> Spec -> Spec
specMapTSpec f s =
    let ?spec = s
    in let tm' = map (tmMapTSpec f) (specTemplate s)
           tx' = map (\t -> t{ txInput   = map (\i -> i{tpType = mapTSpec f ScopeTop $ tpType i}) $ txInput t
                             , txOutput  = map (\o -> o{tpType = mapTSpec f ScopeTop $ tpType o}) $ txOutput t
                             , txBody    = case txBody t of
                                                Left is -> Left is
                                                Right s -> Right $ statMapTSpec f (ScopeTransducer t) s}) 
                     (specTransducer s)
           t'  = map (\t -> TypeDecl (pos t) (mapTSpec f ScopeTop $ tspec t) (name t)) (specType s)
           c'  = map (\c -> Const (pos c) (mapTSpec f ScopeTop $ tspec c) (name c) (constVal c)) (specConst s)
       in Spec tm' t' c' tx'


---------------------------------------------------------------------
-- Flattening
---------------------------------------------------------------------

-- Main flattening function: flatten the spec, producing a spec with a single 
-- template.
flatten :: (MonadError String me) => Spec -> me Spec
flatten s = do
    let s' = mergeParents $ flattenConsts $ flattenTDecls s
    let ?spec = s' 
--    assert (isJust mmain) nopos $ "\"main\" template not found"
--    let main = fromJust mmain
    case find ((== "main") . sname) (specTemplate s') of
         Nothing   -> return s'{specTemplate = []}
         Just main -> do
             mapM validateTmProcesses3 (filter isConcreteTemplate $ specTemplate s')
             checkConcreteTemplate main (pos main)
             assert (null $ tmPort main) (pos main) $ "The main template cannot have ports"
             let gvars = concat $ mapInstTree tmFlattenGVars
                 wires = concat $ mapInstTree tmFlattenWires
                 inits = concat $ mapInstTree tmFlattenInits
                 prefs = concat $ mapInstTree tmFlattenPrefixes
                 procs = concat $ mapInstTree tmFlattenProcs
                 meths = concat $ mapInstTree tmFlattenMeths
                 goals = concat $ mapInstTree tmFlattenGoals
                 rels  = concat $ mapInstTree tmFlattenRels
                 apps  = concat $ mapInstTree tmFlattenApps
                 main' = Template (pos main)
                                  (name main)
                                  []              -- tmPort
                                  []              -- tmDerive
                                  []              -- tmConst
                                  []              -- tmTypeDecl
                                  gvars
                                  wires
                                  []              -- tmInst
                                  inits           -- tmInit
                                  prefs           -- tmPrefix
                                  procs
                                  meths
                                  goals
                                  rels
                                  apps
                 s1 = specSimplify $ s'{specTemplate = [main']}
             validateFlattenedSpec s1
             return s1

-- Remove all pure templates from the spec; merge concrete templates with their parents
mergeParents :: Spec -> Spec
mergeParents s = s{specTemplate = tms}
    where tms = let ?spec = s 
                in map tmMergeParents $ {- filter isConcreteTemplate $-} specTemplate s


-- Move constants from templates to the top level
flattenConsts :: Spec -> Spec
flattenConsts s = s''{specTemplate = map (\t -> t{tmConst = []}) (specTemplate s'')}
    where s'  = let ?spec = s 
                in specMapExpr exprFlattenConsts s
          s'' = foldl' (\s t -> foldl' (\s c -> flattenConst s t c) s (tmConst t)) s' (specTemplate s')
                                   
flattenConst :: Spec -> Template -> Const -> Spec
flattenConst s t c = s{specConst = c':(specConst s)}
    where c' = Const (pos c) (tspec c) (flattenName t c) (constVal c)

-- Move enums from templates to the top level
flattenTDecls :: Spec -> Spec
flattenTDecls s = s''{specTemplate = map (\t -> t{tmTypeDecl = []}) (specTemplate s'')}
    where s'  = let ?spec = s 
                in specMapTSpec tspecFlatten $ specMapExpr exprFlattenEnums s
          s'' = foldl' (\s t -> foldl' (\s d -> flattenTDecl s t d) s (tmTypeDecl t)) s' (specTemplate s')
                                   
flattenTDecl :: Spec -> Template -> TypeDecl -> Spec
flattenTDecl s t d = s{specType = d':(specType s)}
    where d' = case tspec d of
                    sp@(EnumSpec p es) -> TypeDecl (pos d) (flattenEnumSpec t sp) (flattenName t d)
                    sp                 -> TypeDecl (pos d) sp                     (flattenName t d)
        
flattenEnumSpec :: Template -> TypeSpec -> TypeSpec
flattenEnumSpec t (EnumSpec p es) = EnumSpec p (map (\e -> Enumerator (pos e) (flattenName t e)) es)

-- Replace references to constants with flattened names
-- (For use in mapExpr)
exprFlattenConsts :: (?spec::Spec) => Scope -> Expr -> Expr
exprFlattenConsts s e = case e of
                             ETerm p sym  -> case getTerm s sym of
                                                  ObjConst (ScopeTemplate t) c -> ETerm p [flattenName t c]
                                                  _             -> e
                             _            -> e

-- Replace references to enums with flattened names
-- (For use in mapExpr)
exprFlattenEnums :: (?spec::Spec) => Scope -> Expr -> Expr
exprFlattenEnums s e = case e of
                             ETerm p sym  -> case getTerm s sym of
                                                  ObjEnum (Type (ScopeTemplate t) _) en -> ETerm p [flattenName t en]
                                                  _                                     -> e
                             _            -> e

-- Replace references to local types with flattened names
-- (For use in mapTSpec)
tspecFlatten :: (?spec::Spec) => Scope -> TypeSpec -> TypeSpec
tspecFlatten s (UserTypeSpec p n) = 
    case getTypeDecl s n of
         (d, ScopeTop)         -> UserTypeSpec p n
         (d, ScopeTemplate tm) -> UserTypeSpec p [flattenName tm d]
tspecFlatten _ t = t


-----------------------------------------------------------------------------
-- Validation steps performed on the flattened spec
-----------------------------------------------------------------------------

validateFlattenedSpec :: (MonadError String me) => Spec -> me ()
validateFlattenedSpec s = do
    let ?spec = s
    validateSpecCallGraph2
    validateTmWires4
