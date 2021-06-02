{-# LANGUAGE ImplicitParams, TupleSections #-}

module Abstract.CFA2ACFA(ecasAbsVars,
                tranCFAToACFA,
                bexprToFormula,
                bexprToFormulaPlus,
                pruneCFAVar) where

import qualified Data.Graph.Inductive as G
import Data.List
import Data.Maybe
import Data.Functor
import Data.Tuple.Select
import qualified Data.Map as M
import Control.Applicative
import Control.Monad.State

import Util hiding (trace)
import TSLUtil
import Abstract.Cascade
import Abstract.Predicate
import Abstract.BFormula
import Internal.ISpec
import Internal.IExpr
import Internal.IType
import Internal.CFA
import Ops
import Abstract.ACFA
import {-# SOURCE #-} Abstract.MkPredicate

ecasAbsVars :: (?spec::Spec) => ECascade -> [AbsVar]
ecasAbsVars = nub . ecasAbsVars'

ecasAbsVars' :: (?spec::Spec) => ECascade -> [AbsVar]
ecasAbsVars' (CasTree bs) = concatMap (\(f,cas') -> fAbsVars f ++ ecasAbsVars' cas') bs
ecasAbsVars' (CasLeaf e)  = scalarExprAbsVars e 

mecasAbsVars :: (?spec::Spec) => MECascade -> [AbsVar]
mecasAbsVars = nub . mecasAbsVars'

mecasAbsVars' :: (?spec::Spec) => MECascade -> [AbsVar]
mecasAbsVars' (CasTree bs) = concatMap (\(f,cas') -> fAbsVars f ++ mecasAbsVars' cas') bs
mecasAbsVars' (CasLeaf me) = maybe [] scalarExprAbsVars me 

scalarExprAbsVars :: (?spec::Spec) => Expr -> [AbsVar]
scalarExprAbsVars e | (isBool $ exprType e)  = fAbsVars $ ptrFreeBExprToFormula e
                    | otherwise              = case scalarExprToTerm e of 
                                                    TEnum _   -> []
                                                    TUInt _ _ -> []
                                                    TSInt _ _ -> []
                                                    t         -> if' (isInt $ termType t) [AVarInt t] [AVarEnum t]


-- Compute ACFA for a list of abstract variables for a location inside
-- transition CFA. 
tranCFAToACFA :: (?spec::Spec, ?pred::[Predicate]) => [(AbsVar, LogicOp, Expr)] -> Loc -> CFA -> ACFA
tranCFAToACFA vs loc cfa = 
    let ?initloc = loc 
        ?cfa = cfaPruneUnreachable cfa [loc] in 
    let -- prefill ACFA for final states
        acfa0 = foldl' (\g l -> addUseDefVar g l $ map (\v -> (v, l)) vs) G.empty
                $ filter ((==0) . G.outdeg ?cfa)
                $ G.nodes ?cfa
    in simplifyACFA $ mkACFA acfa0 []

mkACFA :: (?spec::Spec, ?initloc::Loc, ?pred::[Predicate], ?cfa::CFA) => ACFA -> [Loc] -> ACFA
mkACFA acfa added = 
    let -- select a location not from the cache with all successors in the cache,
        loc = head
              $ filter (all (\n -> elem n added) . G.suc ?cfa)
              $ filter (\n -> notElem n added)
              $ G.nodes ?cfa
        -- compute variable updates along all outgoing transitions
        updates = map (\(loc', tran) -> (loc', tranPrecondition tran, map (exprUpdateTran tran . sel3) $ fst $ fromJust $ G.lab acfa loc')) $ G.lsuc ?cfa loc
        -- extract the list of abstract variables from transitions
        vs = nub $ concatMap (\(_,mpre,upd) -> maybe [] fAbsVars mpre ++ concatMap mecasAbsVars upd) updates
        acfa'  = addUseDefVar acfa loc $ map (\v -> ((v, Iff, avarToExpr v), exprRecomputedLoc loc $ avarToExpr v)) vs
        acfa'' = foldIdx (\gr (l, pre, upds) i -> G.insEdge (loc, l, (i,pre,upds)) gr) acfa' updates
    in if loc == ?initloc
          then acfa''
          else mkACFA acfa'' (loc:added)

pruneCFAVar :: (?spec::Spec, ?pred::[Predicate]) => [Expr] -> CFA -> CFA
pruneCFAVar es cfa = cfa2
    where
    -- Find all transitions that update variable values
    trs = filter (\(_,_,tr) -> any (\e -> isExprRecomputedByTran e tr) es) 
          $ G.labEdges cfa
    -- Find all predecessors and successors of these transitions
    keepedges = nub $ concatMap (\e@(fr,to,_) -> e : (concatMap (G.inn cfa) (G.rdfs [fr] cfa)) ++
                                                     (concatMap (G.out cfa) (G.dfs [to] cfa))) trs
    keepnodes = nub $ concatMap (\(fr, to, _) -> [fr,to]) keepedges
    -- delete irrelevant nodes
    cfa1 = foldl' (\g l -> if' (elem l keepnodes) g (G.delNode l g)) cfa (G.nodes cfa)
    -- delete irrelevant edges connecting relevant nodes
    cfa2 = foldl' (\g e -> if' (elem e keepedges) g (G.delLEdge e g)) cfa1 (G.labEdges cfa)

exprRecomputedLoc :: (?spec::Spec, ?pred::[Predicate], ?cfa::CFA) => Loc -> Expr -> Loc
exprRecomputedLoc l e = evalState (exprRecomputedLocM l e) M.empty

exprRecomputedLocM :: (?spec::Spec, ?pred::[Predicate], ?cfa::CFA) => Loc -> Expr -> State (M.Map Loc Loc) Loc
exprRecomputedLocM l e = do
    m <- get
    case M.lookup l m of
         Nothing -> do res <- if' (null $ G.pre ?cfa l)                                  (return l) $
                              if' (any (isExprRecomputedByTran e . snd) (G.lpre ?cfa l)) (return l) $
                              do ls <- mapM (\l' -> exprRecomputedLocM l' e) $ G.pre ?cfa l
                                 let (pre0:pres)  = ls
                                 if' (all (== pre0) pres) (return pre0) (return l)
                       modify (\m' -> M.insert l res m')
                       return res
         Just l' -> return l'

isExprRecomputedByTran :: (?spec::Spec, ?pred::[Predicate]) => Expr -> TranLabel -> Bool
isExprRecomputedByTran e tr = case exprUpdateTran tr e of
                                   CasLeaf e' -> e' /= Just e
                                   _          -> True


simplifyACFA :: (?spec::Spec) => ACFA -> ACFA
simplifyACFA acfa = if' (b1 || b2 || b3 || b4 || b5) (simplifyACFA acfa5) acfa
    where (acfa1, b1) = simplifyACFA1 acfa
          (acfa2, b2) = simplifyACFA2 acfa1
          (acfa3, b3) = simplifyACFA3 acfa2
          (acfa4, b4) = simplifyACFA4 acfa3
          (acfa5, b5) = simplifyACFA5 acfa4

-- Find and delete a location that
-- * has a single outgoing transition that does not contain any variable
--   updates or preconditions
simplifyACFA1 :: ACFA -> (ACFA, Bool)
simplifyACFA1 acfa = maybe (acfa, False) ((, True) . rm acfa) mcand
    where mcand = find ((\(_, mpre, upds) -> isNothing mpre && null upds) . snd . head . G.lsuc acfa)
                  $ filter ((==1) . length . G.lsuc acfa)
                  $ filter ((>0)  . length . G.pre acfa)  -- not initial location
                  $ filter (null  . fst . fromJust . G.lab acfa)
                  $ G.nodes acfa
          rm :: ACFA -> Loc -> ACFA
          rm g c = foldl' (\g' (c'', l) -> G.insEdge (c'',c', l) g') (G.delNode c g) (G.lpre g c)
              where c' = head $ G.suc g c

-- Find a location that
-- * has a single outgoing edge to a location that only has one predecessor
-- * this edge does not contain preconditions or variable updates
-- and delete this successor location
simplifyACFA2 :: ACFA -> (ACFA, Bool)
simplifyACFA2 acfa = maybe (acfa, False) ((, True) . rm acfa) mcand
    where mcand = find ((\(_, mpre, upds) -> isNothing mpre && null upds) . snd . head . G.lsuc acfa)
                  $ filter ((==1) . length . G.pre acfa . head . G.suc acfa)
                  $ filter ((==1) . length . G.lsuc acfa)
                  $ filter ((>0)  . length . G.pre acfa)
                  $ G.nodes acfa
          rm :: ACFA -> Loc -> ACFA
          rm g c = foldl' (\g' (c'', l) -> G.insEdge (c,c'', l) g') (G.delNode c' g0) (G.lsuc g0 c')
              where (def,_) = fromJust $ G.lab g c
                    c' = head $ G.suc g c
                    (_,use) = fromJust $ G.lab g c' 
                    g0 = graphUpdNode c (\_ -> (def,use)) g


-- eliminate conditional nodes (i.e., nodes that have 2 outgoing edges labelled 
-- with complementary preconditions, but no var updates) in case they only have a 
-- single successor.  The assumption here is that all branches are of the form 
-- if-then-else, i.e., disjunction of branch conditions is true.
simplifyACFA3 :: ACFA -> (ACFA, Bool)
simplifyACFA3 acfa = maybe (acfa, False) ((,True) . rm acfa) mcand
    where mcand = find ((\[pre1,pre2] -> pre2 == FNot pre1 || pre1 == FNot pre2) . map (fromJust . sel2 . snd) . G.lsuc acfa)
                  $ filter     (all ((\(_,mpre,upd) -> null upd && isJust mpre) . snd) . G.lsuc acfa)
                  $ filter ((==1) . length . nub . G.suc acfa)
                  $ filter ((==2)  . length . G.lsuc acfa)
                  $ G.nodes acfa     
          rm :: ACFA -> Loc -> ACFA
          rm g c = graphUpdNode c (\(def, _) -> (def,M.empty))
                   $ G.insEdge (c, c', (0, Nothing, [])) 
                   $ G.delEdge (c,c') g
                   where c' = head $ G.suc g c

-- Prune references to variables that are not used anymore
simplifyACFA4 :: (?spec::Spec) => ACFA -> (ACFA, Bool)
simplifyACFA4 acfa = foldl' (\(acfa',f') (l, (r,defs)) -> let u = used l 
                                                              defs' = M.filterWithKey (\av _ -> elem av u) defs in
                                                          (graphUpdNode l (\_ -> (r, defs')) acfa', f' || (M.size defs' /= M.size defs))) 
                            (acfa, False) (G.labNodes acfa)
    where 
    used :: Loc -> [AbsVar]
    used loc | null (G.lsuc acfa loc) = M.keys $ snd $ fromJust $ G.lab acfa loc -- don't trim final location
             | otherwise              = nub $ concatMap (\(_,(_,mpre,upds)) -> (maybe [] fAbsVars mpre) ++ concatMap mecasAbsVars upds) $ G.lsuc acfa loc

-- Detemine variables recomputed at different locations that are still used somewhere else
-- and don't recompute variables that are not needed.
simplifyACFA5 :: ACFA -> (ACFA, Bool)
simplifyACFA5 acfa = (G.gmap rm acfa, f)
    where
    used = concatMap (M.toList . snd . snd) $ G.labNodes acfa
    cands = M.fromList $ map (\(loc, (recomp, _)) -> (loc, getCands loc recomp)) $ G.labNodes acfa
    getCands loc avs = findIndices (\(av,_,_) -> notElem (av,loc) used) avs
    f = any (\(loc, (recomp,_)) -> not $ null $ getCands loc recomp) $ G.labNodes acfa
    rm (pre, loc, (recomp, defs), suc) = (pre', loc, (recomp',defs), suc')
        where
        delIndices is lst = catMaybes $ mapIdx (\x i -> if' (elem i is) Nothing (Just x)) lst
        recomp' = delIndices (cands M.! loc) recomp
        pre' = map (mapFst (mapTrd3 (delIndices (cands M.! loc)))) pre
        suc' = map (\(e, loc') -> (mapTrd3 (delIndices (cands M.! loc')) e, loc')) suc


-- Takes a location and a list of variables used in this location and updates
-- the corresponding use and defined lists.
addUseDefVar :: ACFA -> Loc -> [((AbsVar, LogicOp, Expr), Loc)] -> ACFA
addUseDefVar acfa useloc defs = 
    foldl' (\acfa' (v, defloc) -> let acfa1 = graphUpdNode useloc (\(def, use) -> (def, M.insert (sel1 v) defloc use)) acfa'
                                  in case G.lab acfa1 defloc of
                                          Nothing -> G.insNode (defloc, ([v], M.empty)) acfa1
                                          Just _  -> graphUpdNode defloc (\(def, use) -> (nub $ v:def, use)) acfa1)
           acfa0 defs
    where
    acfa0 = case G.lab acfa useloc of
                 Nothing -> G.insNode (useloc, ([], M.empty)) acfa
                 Just _  -> acfa

-- Precondition of a transition
tranPrecondition :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> Maybe Formula
tranPrecondition (TranStat (SAssume e))   = Just $ ptrFreeBExprToFormula e
tranPrecondition _                        = Nothing

-- Compute variable updates for an individual CFA edge
exprUpdateTran :: (?spec::Spec, ?pred::[Predicate]) => TranLabel -> Expr -> MECascade
exprUpdateTran (TranStat (SAssign e1 e2)) e = fmap (fmap (\e_ -> if' (isConstExpr e_) (EConst $ evalConstExpr e_) e_)) 
                                              $ updateExprAsn e1 e2 e
exprUpdateTran _                          e = CasLeaf $ Just e

updateExprAsn :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> MECascade
updateExprAsn lhs rhs e = casMap (updateExprAsn' lhs rhs) $ updateExprIndices lhs rhs e

updateExprAsn' :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> MECascade
updateExprAsn' lhs rhs e@(EVar _)          = Just <$> updateScalAsn lhs rhs e
updateExprAsn' _   _   e@(EConst _)        = CasLeaf $ Just e
updateExprAsn' lhs rhs e@(EField _ _)      = Just <$> updateScalAsn lhs rhs e
updateExprAsn' lhs rhs e@(EIndex _ _)      = Just <$> updateScalAsn lhs rhs e
updateExprAsn' _   _   e@(EUnOp AddrOf _)  = CasLeaf $ Just e
updateExprAsn' lhs rhs   (EUnOp op e)      = fmap (EUnOp op) <$> updateExprAsn' lhs rhs e
updateExprAsn' lhs rhs   (EBinOp op e1 e2) = (\me1 me2 -> EBinOp op <$> me1 <*> me2) 
                                              <$> updateExprAsn' lhs rhs e1
                                              <*> updateExprAsn' lhs rhs e2
updateExprAsn' lhs rhs   (ESlice e s)      = fmap (\e' -> exprSlice e' s) <$> updateExprAsn' lhs rhs e
updateExprAsn' lhs rhs   (ERel n as)       = (\mas -> sequence mas >>= (return . ERel n))
                                             <$> foldl' (\cas a -> (\es e -> es ++ [e]) <$> cas <*> (updateExprAsn' lhs rhs a)) (CasLeaf []) as
updateExprAsn' lhs rhs   (ELength a)       = (fmap ELength) <$> updateExprAsn' lhs rhs a
updateExprAsn' lhs rhs   (ERange a (f,l))  = updateRange lhs rhs a f l

-- Update range expression:
-- if lhs is within range, then the value is undefined; otherwise
-- the value does not change
updateRange :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> Expr -> Expr -> MECascade
updateRange lhs _ a f l = let ident = CasLeaf $ Just $ ERange a (f,l) in
                          casMap (maybe ident 
                                        (\i -> let inrange = ptrFreeBExprToFormula $ (plusmod a [i, uminus f]) .<= plusmod a [l]
                                               in (casTree [(inrange     , CasLeaf Nothing), 
                                                            (fnot inrange, ident)])))
                                 $ lexprInArray lhs a

-- Computes conditions when lhs is contained within a
-- Returns cascade where leaves represent array index where lhs is stored
lexprInArray :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> MECascade
lexprInArray (ESlice e  _) a                   = lexprInArray e a
lexprInArray (EField e  _) a                   = lexprInArray e a
lexprInArray (EIndex a' i) a | isomorphic a' a = fmap (\b -> if' b (Just i) Nothing) $ lhsExprEq a' a
                             | otherwise       = lexprInArray a' a
                             where isomorphic (EVar v1)      (EVar v2)      = v1 == v2
                                   isomorphic (EIndex a1 _)  (EIndex a2 _)  = isomorphic a1 a2
                                   isomorphic (EField e1 f1) (EField e2 f2) = isomorphic e1 e2 && f1 == f2
                                   isomorphic _             _               = False
lexprInArray (EVar _)      _                   = CasLeaf Nothing

-- apply updateExprAsn to all array indices in the expression
updateExprIndices :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateExprIndices _   _   e@(EVar _)          = CasLeaf e
updateExprIndices _   _   e@(EConst _)        = CasLeaf e
updateExprIndices lhs rhs   (EField s f)      = (\s' -> EField s' f) <$> updateExprIndices lhs rhs s
updateExprIndices lhs rhs   (EIndex a i)      = EIndex               <$> updateExprIndices lhs rhs a <*> fmap fromJust (updateExprAsn lhs rhs i)
updateExprIndices lhs rhs   (EUnOp op e)      = EUnOp op             <$> updateExprIndices lhs rhs e
updateExprIndices lhs rhs   (EBinOp op e1 e2) = (EBinOp op)          <$> updateExprIndices lhs rhs e1 <*> updateExprIndices lhs rhs e2
updateExprIndices lhs rhs   (ESlice e s)      = (\e' -> ESlice e' s) <$> updateExprIndices lhs rhs e
updateExprIndices lhs rhs   (ERel n as)       = (ERel n)             <$> foldl' (\cas a -> (\es e -> es ++ [e]) <$> cas <*> (updateExprIndices lhs rhs a)) (CasLeaf []) as
updateExprIndices lhs rhs   (ELength a)       = ELength              <$> updateExprIndices lhs rhs a 
updateExprIndices lhs rhs   (ERange a (f,l))  = ERange               <$> updateExprIndices lhs rhs a <*>
                                                                     ((,) <$> (fmap fromJust (updateExprAsn lhs rhs f))
                                                                          <*> (fmap fromJust (updateExprAsn lhs rhs l)))

-- Takes lhs and rhs of assignment statement and a term
-- Computes possible overlaps of the lhs with the term and
-- corresponding next-state values of the term expressed as concatenation 
-- of slices of the rhs and the original term.
updateScalAsn :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateScalAsn lhs rhs x = casMap exprExpandPtr $ updateScalAsn' lhs rhs x

updateScalAsn' :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> Expr -> ECascade
updateScalAsn' lhs              rhs (ESlice x s) = fmap (\e' -> exprSlice e' s) (updateScalAsn' lhs rhs x)
updateScalAsn' (ESlice e (l,h)) rhs x            = 
    fmap (\b -> if b
                   then econcat $
                        (if l == 0 then [] else [exprSlice x (0,l-1)]) ++
                        [rhs] ++
                        (if h == w - 1 then [] else [exprSlice x (h+1, w - 1)])
                   else x) 
         $ lhsExprEq e x
    where w = exprWidth e
updateScalAsn' lhs              rhs x            = 
    fmap (\b -> if b then rhs else x) $ lhsExprEq lhs x


-- Takes lhs expression and a term and computes the condition 
-- when the expression is a synonym of the term.
lhsExprEq :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Expr -> BCascade
lhsExprEq (EVar n1)      (EVar n2)        | n1 == n2 = CasLeaf True
lhsExprEq (EField e1 f1) (EField e2 f2)   | f1 == f2 = lhsExprEq e1 e2
lhsExprEq (EIndex a1 i1) (EIndex a2 i2)              = 
    casMap (\b -> if' b 
                     (case bexprToFormula $ i1 === i2 of
                           FTrue  -> CasLeaf True
                           FFalse -> CasLeaf False
                           f      -> casTree [(f, CasLeaf True), (fnot f, CasLeaf False)])
                     (CasLeaf False))
           $ lhsExprEq a1 a2
lhsExprEq (EUnOp Deref e1) e2             | t1 == t2 && isMemExpr e2 = 
    case bexprToFormula $ e1 === EUnOp AddrOf e2 of
         FTrue  -> CasLeaf True
         FFalse -> CasLeaf False
         f      -> casTree [(f, CasLeaf True), (fnot f, CasLeaf False)]
    where Ptr _ t1 = exprType e1
          t2       = exprType e2
lhsExprEq _              _                           = CasLeaf False


-- Convert boolean expression (possibly with pointers) to a formula without
-- introducing new pointer predicates.
bexprToFormula :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Formula
bexprToFormula e = fcasToFormula $ fmap ptrFreeBExprToFormula $ exprExpandPtr e

-- Convert boolean expression (possibly with pointers) to a formula, 
-- introducing new pointer predicates if needed.
bexprToFormulaPlus :: (?spec::Spec, ?pred::[Predicate]) => Expr -> Formula
bexprToFormulaPlus e@(EBinOp op e1 e2) | op == Eq || op == Neq = 
    let f1 = case e1 of
                  EUnOp Deref e1' -> fcasToFormula $ fcasPrune $ (addrPred op) <$> (exprExpandPtr e1') <*> (exprExpandPtr e2)
                  _               -> FFalse
        f2 = case e2 of
                  EUnOp Deref e2' -> fcasToFormula $ fcasPrune $ (addrPred op) <$> (exprExpandPtr e2') <*> (exprExpandPtr e1)
                  _               -> FFalse
    in fdisj $ (bexprToFormula e):[f1,f2]

bexprToFormulaPlus e = bexprToFormula e

-- Check if predicate (x == addrof y) exists in the DB.  If yes,
-- return false, else return (x == addrof y) or !(x == addrof y),
-- depending on op.
addrPred :: (?spec::Spec, ?pred::[Predicate]) => BOp -> Expr -> Expr -> Formula
addrPred op x y =
    let fp = fRel REq x (EUnOp AddrOf y)
    in if (not $ isMemExpr y) || (any ((==y) . termToExpr . snd) $ ptrPreds x)
          then FFalse
          else if op == Eq
                  then fp 
                  else fnot fp


-- Expand each pointer dereference operation in the expression
-- using predicates in the DB.
exprExpandPtr :: (?pred::[Predicate]) => Expr -> ECascade
exprExpandPtr e@(EVar _)          = CasLeaf e
exprExpandPtr e@(EConst _)        = CasLeaf e
exprExpandPtr   (EField e f)      = (\e' -> EField e' f) <$> exprExpandPtr e
exprExpandPtr   (EIndex a i)      = EIndex               <$> exprExpandPtr a <*> exprExpandPtr i
exprExpandPtr   (EUnOp Deref e)   = casMap (casTree . (map (\(p, t) -> (FBoolAVar $ AVarPred p, CasLeaf $ termToExpr t))) . ptrPreds)
                                           $ exprExpandPtr e
exprExpandPtr   (EUnOp op e)      = EUnOp op             <$> exprExpandPtr e
exprExpandPtr   (EBinOp op e1 e2) = EBinOp op            <$> exprExpandPtr e1 <*> exprExpandPtr e2
exprExpandPtr   (ESlice e s)      = (\e' -> ESlice e' s) <$> exprExpandPtr e
exprExpandPtr   (ERel r as)       = (ERel r)             <$> foldl' (\cas a -> (\es e -> es ++[e]) <$> cas <*> (exprExpandPtr a)) (CasLeaf []) as
exprExpandPtr   (ERange a (f,l))  = ERange               <$> exprExpandPtr a <*> ((,) <$> exprExpandPtr f <*> exprExpandPtr l)
exprExpandPtr   e                 = error $ "exprExpandPtr " ++ show e

-- Find predicates of the form (e == AddrOf e')
ptrPreds :: (?pred::[Predicate]) => Expr -> [(Predicate, Term)]
ptrPreds e = 
    mapMaybe (\p -> case p of
                         PAtom PEq (PTPtr t1) (PTPtr t2) -> if' (termToExpr t1 == e) 
                                                                (case t2 of
                                                                      TAddr t' -> Just (p,t')
                                                                      _        -> Nothing)
                                                                (if' (termToExpr t2 == e)
                                                                     (case t1 of
                                                                           TAddr t' -> Just (p,t')
                                                                           _        -> Nothing)
                                                                     Nothing)
                         _                               -> Nothing)
             ?pred
