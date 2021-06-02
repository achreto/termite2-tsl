{-# LANGUAGE FlexibleContexts, ImplicitParams, TupleSections, RecordWildCards #-}

module Frontend.TemplateOps(tmMapExpr,
                   tmMapTSpec,
                   tmPure,
                   isConcreteTemplate,
                   drvGraph,
                   instGraph,
                   callGraph,
                   isDescendant,
                   tmPathTo,
                   tmParents,
                   tmParentsRec,
                   tmLabels,
                   tmAllGoal,
                   tmAllMethod,
                   tmAllProcess,
                   tmSubprocess,
                   tmAllInit,
                   tmAllInst,
                   tmAllWire,
                   tmAllVar,
                   tmLookupPortInst,
                   tmLocalDecls,
                   tmLocalAndParentDecls,
                   tmScopes,
                   wireType,
                   callees,
                   tmMergeParents) where

import Data.List
import Data.Maybe
import qualified Data.Map as M
import Control.Monad.Except
import qualified Data.Graph.Inductive.Graph     as G
import qualified Data.Graph.Inductive.Tree      as G
import qualified Data.Graph.Inductive.Query.DFS as G

import Util hiding (name)
import TSLUtil
import Pos
import Name
import Frontend.Type
import Frontend.TypeOps
import Frontend.Template
import Frontend.Spec
import Frontend.Const
import Frontend.TVar
import Frontend.TVarOps
import {-# SOURCE #-} Frontend.MethodOps
import Frontend.Expr
import {-# SOURCE #-} Frontend.ExprOps
import Frontend.Method
import Frontend.Process
import Frontend.Statement
import Frontend.StatementOps
import Frontend.NS
import Frontend.Relation

-- Map function over all expressions occurring in the template
tmMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Template -> Template
tmMapExpr f tm = tm { tmConst    = map (\c -> c{constVal = mapExpr f s (constVal c)})                                 (tmConst tm)
                    , tmTypeDecl = map (\t -> TypeDecl (pos t) (tspecMapExpr f s $ tspec t) (name t))                 (tmTypeDecl tm)
                    , tmVar      = map (\v -> v{gvarVar = varMapExpr f s (gvarVar v)})                                (tmVar tm)
                    , tmWire     = map (\w -> w{wireTSpec = tspecMapExpr f s (wireTSpec w), 
                                                wireRHS  = fmap (mapExpr f s) (wireRHS w)})                           (tmWire tm)
                    , tmInit     = map (\i -> i{initBody = mapExpr f s (initBody i)})                                 (tmInit tm)
                    , tmPrefix   = map (\a -> a{prefBody = statMapExpr f s (prefBody a)})                             (tmPrefix tm)
                    , tmProcess  = map (\p -> p{procStatement = statMapExpr f (ScopeProcess tm p) (procStatement p)}) (tmProcess tm)
                    , tmRelation = map (\r -> let sr = ScopeRelation tm r in
                                              r{relRule = map (\rl -> rl{ruleExpr = mapExpr f sr (ruleExpr rl)}) (relRule r)}) (tmRelation tm)
                    , tmApply    = map (\a -> a{applyArg = map (mapExpr f s) (applyArg a)})                           (tmApply tm)
                    , tmMethod   = map (\m -> let sm = ScopeMethod tm m in
                                              m{methRettyp = fmap (tspecMapExpr f s) (methRettyp m),
                                                methArg    = map (\a -> a{argTSpec = tspecMapExpr f s (argTSpec a)})  (methArg m),
                                                methBody   = case methBody m of
                                                                  Left (mb,ma) -> Left  $ (fmap (statMapExpr f sm) mb, fmap (statMapExpr f sm) ma)
                                                                  Right b      -> Right $ statMapExpr f sm b})        (tmMethod tm)
                    , tmGoal     = map (\g -> g{goalCond = mapExpr f s (goalCond g)})                                 (tmGoal tm)}
    where s = ScopeTemplate tm

-- Map function over all TypeSpec's occurring in the template
tmMapTSpec :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Template -> Template
tmMapTSpec f tm = tm { tmConst    = map (\c -> Const (pos c) (mapTSpec f s $ tspec c) (name c) (constVal c))               (tmConst tm)
                     , tmTypeDecl = map (\t -> TypeDecl (pos t) (mapTSpec f s $ tspec t) (name t))                         (tmTypeDecl tm)
                     , tmVar      = map (\v -> v{gvarVar  = (gvarVar v){varTSpec = mapTSpec f s $ tspec v}})               (tmVar tm)
                     , tmWire     = map (\w -> w{wireTSpec = mapTSpec f s (wireTSpec w)})                                  (tmWire tm)
                     , tmPrefix   = map (\a -> a{prefBody = statMapTSpec f s (prefBody a)})                                (tmPrefix tm)
                     , tmProcess  = map (\p -> p{procStatement = statMapTSpec f s (procStatement p)})                      (tmProcess tm)
                     , tmRelation = map (\r -> r{relArg = map (\a -> a{rargTSpec = mapTSpec f s (rargTSpec a)}) (relArg r)}) (tmRelation tm)
                     , tmMethod   = map (\m -> let sm = ScopeMethod tm m in
                                               m{methRettyp = fmap (mapTSpec f s) (methRettyp m),
                                                 methArg    = map (\a -> a{argTSpec = mapTSpec f s (argTSpec a)}) (methArg m),
                                                 methBody   = case methBody m of
                                                                   Left (mb,ma) -> Left  $ (fmap (statMapTSpec f sm) mb, fmap (statMapTSpec f s) ma)
                                                                   Right b      -> Right $ statMapTSpec f sm b})           (tmMethod tm)}
    where s = ScopeTemplate tm


tmPure :: (?spec::Spec) => Template -> ([Method],[Wire])
tmPure tm = (purem, purew)
    where purem = filter (\m -> case methFullBody tm m of
                                     Left  _ -> True
                                     Right _ -> False)
                         (tmAllMethod tm)
          purew = filter (isNothing . wireRHS) (tmAllWire tm)

isConcreteTemplate :: (?spec::Spec) => Template -> Bool
isConcreteTemplate t = case tmPure t of
                            ([],[]) -> True
                            _       -> False

-------------------------------------------------------------------
-- Instantiation graph
-------------------------------------------------------------------

type InstGraph = G.Gr Ident ()

instGraph :: (?spec::Spec) => InstGraph
instGraph = 
    let tmap = M.fromList $ zip (map name $ specTemplate ?spec) [1..]
        gnodes = foldl' (\g t -> G.insNode (tmap M.! name t, name t) g) G.empty (specTemplate ?spec)
    in foldl' (\g t -> foldl' (\g' i -> G.insEdge (tmap M.! name t, tmap M.! instTemplate i, ()) g')
                              g (tmAllInst t))
              gnodes (specTemplate ?spec)

-------------------------------------------------------------------
-- Derivation graph
-------------------------------------------------------------------

type DrvGraph = (G.Gr Ident (), M.Map Ident Int)


-- construct template derivation graph
drvGraph :: (?spec::Spec) => DrvGraph
drvGraph = (g,tmap)
    where tmap = M.fromList $ zip (map name $ specTemplate ?spec) [1..]
          gnodes = foldl' (\g' t -> G.insNode (tmap M.! name t, name t) g') G.empty (specTemplate ?spec)
          g = foldl' (\g' t -> foldl' (\g'' d -> G.insEdge (tmap M.! name t, tmap M.! drvTemplate d, ()) g'')
                                      g' (tmDerive t))
                     gnodes (specTemplate ?spec)


-------------------------------------------------------------------
-- Call graph
-------------------------------------------------------------------

type CallGraph = G.Gr Scope Pos

tmScopes :: (?spec::Spec) => Template -> [Scope]
tmScopes tm = (map (ScopeProcess tm) (tmAllProcess tm)) ++ (map (ScopeMethod tm) (tmAllMethod tm))

callees :: (?spec::Spec) => Scope -> [(Pos, (Template, Method))]
callees s@(ScopeProcess _ p) = statCallees s (procStatement p)
callees s@(ScopeMethod t m)  = statCallees s b
    where Right b = methFullBody t m

callGraph :: (?spec::Spec) => CallGraph
callGraph = 
    let scopes = concatMap tmScopes $ filter isConcreteTemplate $ specTemplate ?spec
        gnodes = foldIdx (\g s i -> G.insNode (i, s) g) G.empty scopes
    in foldIdx (\g s i -> foldl' (\g' (p,(t,m)) -> G.insEdge (i, fromJust $ findIndex (==ScopeMethod t m) scopes, p) g')
                                 g (callees s))
               gnodes scopes

-------------------------------------------------------------------
-- Wires
-------------------------------------------------------------------

wireType :: (?spec::Spec, ?scope::Scope) => Wire -> Type
wireType = Type ?scope . tspec

-------------------------------------------------------------------
-- Namespace-related stuff
-------------------------------------------------------------------

-- Path to object through class hierarchy 
tmPathTo :: (?spec::Spec) => Template -> Ident -> [Ident]
tmPathTo t n = fromJust $ tmPathTo' t n

tmPathTo' :: (?spec::Spec) => Template -> Ident -> Maybe [Ident]
tmPathTo' t@Template{..} n = 
    -- search parents first to find the earliest declaration
    case parpath of 
         Nothing -> localpath
         Just p  -> Just p
    where parpath = listToMaybe $ mapMaybe (\d -> fmap (drvTemplate d :) $ tmPathTo' (getTemplate $ drvTemplate d) n) tmDerive
          localpath = fmap (\_ -> []) $ find ((==n) . name) $ tmLocalDecls t
                          
tmLocalDecls :: (?spec::Spec) => Template -> [Obj]
tmLocalDecls t = (map (ObjPort t)                     (tmPort t))     ++
                 (map (ObjConst (ScopeTemplate t))    (tmConst t))    ++
                 (map (ObjTypeDecl (ScopeTemplate t)) (tmTypeDecl t)) ++
                 (map (ObjGVar t)                     (tmVar t))      ++
                 (map (ObjWire t)                     (tmWire t))     ++
                 (map (ObjInstance t)                 (tmInst t))     ++
                 (map (ObjProcess t)                  (tmProcess t))  ++
                 (map (ObjMethod t)                   (tmMethod t))   ++
                 (map (ObjGoal t)                     (tmGoal t))     ++
                 (map (ObjRelation t)                 (tmRelation t)) ++
                 (concat $ map (\d -> case tspec d of
                                           EnumSpec _ es -> map (ObjEnum (Type (ScopeTemplate t) $ tspec d)) es
                                           _             -> []) (tmTypeDecl t))


tmLabels :: (?spec::Spec) => Template -> [Ident]
tmLabels tm = (concatMap (statLabels . procStatement) $ tmAllProcess tm) ++
              (concatMap methLabels $ tmAllMethod tm)

-- All objects declared in the template or inherited from parents
tmLocalAndParentDecls :: (?spec::Spec) => Template -> [Obj]
tmLocalAndParentDecls t = concat $ (tmLocalDecls t):parents
    where parents = map (tmLocalAndParentDecls . getTemplate . drvTemplate) (tmDerive t)


-- Get parent templates
tmParents :: (?spec::Spec) => Template -> [Template]
tmParents t = map (getTemplate . drvTemplate) (tmDerive t)

tmParentsRec :: (?spec::Spec) => Template -> [Template]
tmParentsRec t = concatMap (\t' -> t':(tmParentsRec t')) $ tmParents t

-- Find port or instance by name.  Returns the name of the associated template.
tmLookupPortInst :: (MonadError String me) => Template -> Ident -> me Ident
tmLookupPortInst t n = case listToMaybe $ catMaybes [p, i] of
                            Nothing -> err (pos n) $ "Unknown port or instance name " ++ show n
                            Just tn -> return tn
    where p = fmap (portTemplate) $ find ((== n) . name) (tmPort t)
          i = fmap (instTemplate) $ find ((== n) . name) (tmInst t)

isDescendant :: (?spec::Spec) => Template -> Template -> Bool
isDescendant anc des = 
    let (g,m) = drvGraph 
        ancid = m M.! (name anc)
        desid = m M.! (name des)
    in elem ancid (G.reachable desid g)

tmSubprocess :: (?spec::Spec) => Template -> [(Ident, Scope, Statement)]
tmSubprocess tm = map (\p -> (name p, ScopeTemplate tm, procStatement p)) (tmProcess tm) ++
                  concatMap (\(sc,st) -> map (\st' -> (fromJust $ stLab st',sc,st')) $ statSubprocessRec st) stats
    where stats = map (\p -> (ScopeProcess tm p, procStatement p)) (tmProcess tm) ++ 
                  map (\m -> (ScopeMethod  tm m, fromRight $ methBody m)) (tmMethod tm)


tmAllVar :: (?spec::Spec) => Template -> [GVar]
tmAllVar t = concatMap (\o -> case o of
                                    ObjGVar _ v -> [v]
                                    _           -> []) 
                       (tmLocalAndParentDecls t)

tmAllInst :: (?spec::Spec) => Template -> [Instance]
tmAllInst t = concatMap (\o -> case o of
                                    ObjInstance _ i -> [i]
                                    _               -> []) 
                        (tmLocalAndParentDecls t)

tmAllInit :: (?spec::Spec) => Template -> [Init]
tmAllInit t = tmInit t ++ (concatMap tmAllInit (tmParents t))

tmAllPrefix :: (?spec::Spec) => Template -> [Prefix]
tmAllPrefix t = tmPrefix t ++ (concatMap tmAllPrefix (tmParents t))

tmAllProcess :: (?spec::Spec) => Template -> [Process]
tmAllProcess t = concatMap (\o -> case o of
                                       ObjProcess _ p -> [p]
                                       _              -> []) 
                           (tmLocalAndParentDecls t)

tmAllGoal :: (?spec::Spec) => Template -> [Goal]
tmAllGoal t = concatMap (\o -> case o of
                                    ObjGoal _ g -> [g]
                                    _           -> []) 
                        (tmLocalAndParentDecls t)

tmAllRelation :: (?spec::Spec) => Template -> [Relation]
tmAllRelation t = concatMap (\o -> case o of
                                        ObjRelation _ r -> [r]
                                        _               -> []) 
                            (tmLocalAndParentDecls t)

tmAllApply :: (?spec::Spec) => Template -> [Apply]
tmAllApply t = tmApply t ++ (concatMap tmAllApply (tmParents t))

tmAllMethod :: (?spec::Spec) => Template -> [Method]
tmAllMethod t = map (\(t',m) -> m{methBody = methFullBody t' m}) $ tmAllMethod' t
                
tmAllMethod' :: (?spec::Spec) => Template -> [(Template,Method)]
tmAllMethod' t = (map (t,) $ tmMethod t) ++
                 (filter (\(_,m) -> not $ elem (name m) $ map name $ tmMethod t) $ 
                         concatMap tmAllMethod' (tmParents t))

tmAllWire :: (?spec::Spec) => Template -> [Wire]
tmAllWire t = tmWire t ++
              (filter (\w -> not $ elem (name w) $ (map name $ tmWire t)) $ 
                      concatMap tmAllWire (tmParents t))


-- Merge template with its parents
-- Assumes that constants and enums have already been flattened
tmMergeParents :: (?spec::Spec) => Template -> Template
tmMergeParents tm = Template (pos tm)
                             (name tm)
                             (tmPort tm)
                             []                    -- tmDerive
                             []                    -- tmConst
                             []                    -- tmTypeDecl
                             (tmAllVar tm)
                             (tmAllWire tm)
                             (tmAllInst tm)
                             (tmAllInit tm)
                             (tmAllPrefix tm)
                             (tmAllProcess tm)
                             (tmAllMethod tm)
                             (tmAllGoal tm)
                             (tmAllRelation tm)
                             (tmAllApply tm)
