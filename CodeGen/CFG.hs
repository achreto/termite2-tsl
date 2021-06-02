{-# LANGUAGE ImplicitParams, RecordWildCards, TemplateHaskell, TupleSections, ConstraintKinds, FlexibleContexts #-}

module CodeGen.CFG (Step(..),
            Branch(..),
            gen1Step,
            derefStep,
            ppStep) where

import Data.Maybe
import Data.Tuple.Select
import qualified Data.Map          as M
import Control.Monad.Except
import Data.List
import qualified Text.PrettyPrint  as PP

import Synthesis.Resource
import Pos
import PP
import TSLUtil
import Util
import Name
import Synthesis.Interface
import Synthesis.TermiteGame
import Synthesis.BddRecord
import Synthesis.RefineCommon
import Abstract.Predicate
import Abstract.BFormula
import CodeGen.AbsSim
import Synthesis.CG as CG
import CodeGen.CodeGen
import Internal.ISpec hiding (getVar)
import Internal.IType
import Internal.IVar
import Frontend.Inline
import Internal.PID
import Solver.BVSMT
import Frontend.InstTree
import Frontend.Method
import Frontend.Expr
import qualified Frontend.NS                as F
import qualified Frontend.Spec              as F
import qualified Frontend.Type              as F
import qualified Frontend.TypeOps           as F
import qualified Frontend.MethodOps         as F
import qualified Internal.IExpr             as I
import qualified Cudd.Imperative            as C
import qualified Synthesis.BddUtil          as C

condFuncRemove :: (RM s u t) => Ops s u -> DDNode s u -> DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
condFuncRemove Ops{..} set care removeCube = do
    avlAndSet  <- $r2 band set care
    noUnwanted <- $r1 (bexists removeCube) avlAndSet
    cond       <- $r2 liCompact noUnwanted care
    $d deref noUnwanted
    condAndSet <- $r2 band cond care
    if condAndSet == avlAndSet 
        then do $d deref avlAndSet
                $d deref condAndSet
                return cond
        else do $d deref avlAndSet
                $d deref condAndSet
                $d deref cond
                $rp ref set
                return set

condRemoveSpecialVars :: (RM s u t, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> DDNode s u -> t (ST s) (DDNode s u)
condRemoveSpecialVars set care = do
    let DB{_symbolTable = SymbolInfo{..}, ..} = ?db
    let ops@Ops{..} = constructOps ?m
    removeCube <- $r $ nodesToCube
                  $ concatMap (sel1 . snd)
                  $ filter (elem '$' . show . fst) -- filter special vars
                  $ M.toList _stateVars 
    res <- condFuncRemove ops set care removeCube
    $d deref removeCube
    return res


data Branch s u = BranchITE    (DDNode s u, DDNode s u) (DDNode s u) (Branch s u)
                | BranchAction (DDNode s u) (DDNode s u)
                | BranchStuck  String

-- A single synthesised step, consisting of a wait condition and
-- an if-then-else fork.
data Step s u = Step { stepWaitCond :: (DDNode s u, DDNode s u) -- (condition,  care set)
                     , stepBranches :: Branch s u 
                     }

ppStep :: (RM s u t) => F.Spec -> F.Spec -> Spec -> PrID -> C.DDManager s u -> F.Scope -> DB s u AbsVar AbsVar -> Step s u -> t (ST s) PP.Doc
ppStep inspec flatspec spec pid m sc pdb Step{..} = do
    let ?inspec   = inspec
        ?flatspec = flatspec
        ?spec     = spec
        ?pid      = pid
        ?m        = m
        ?sc       = sc
        ?db       = pdb
    wait <- if fst stepWaitCond == C.bOne m
               then return PP.empty
               else do cond <- ppCond stepWaitCond
                       return $ PP.text "wait" PP.<> PP.parens cond PP.<> PP.char ';'
    bs <- ppBranch stepBranches True
    return $ wait PP.$+$ (PP.vcat $ PP.punctuate PP.semi bs) 

ppBranch :: (RM s u t, ?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) 
         => Branch s u -> Bool -> t (ST s) [PP.Doc]
ppBranch (BranchStuck reason) _     = return $ [PP.text $ "/* stuck: " ++ reason ++ " */"]
ppBranch (BranchITE i t e) addmb = do
    cond <- ppCond i
    tact <- ppAction t False
    ebr  <- ppBranch e False
    return $ (mkITE cond tact ebr) : if' addmb [PP.text "..."] []
ppBranch (BranchAction _ a) addmb = ppAction a addmb

ppCond :: (RM s u t, ?inspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) 
       => (DDNode s u, DDNode s u) -> t (ST s) PP.Doc
ppCond cond = do 
    conds <- (liftM $ map $ exprToTSL2 ?inspec ?pid ?sc) $ mkCondition cond
    return $ PP.vcat $ PP.punctuate (PP.text "||") conds


ppAction :: (RM s u t, ?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) 
         => DDNode s u -> Bool -> t (ST s) [PP.Doc]
ppAction lab addmb = do
    asns <- mkLabel lab
    let lvars = nub $ map varName $ filter ((==VarTmp) . varCat) $ concatMap (avarVar . fst) asns
    let sol = bvSolve asns lvars
    case sol of
         [] -> return $ [PP.text $ "/* could not concretise label: " ++ show asns ++ " */"]
         _  -> return $ ppAction' sol addmb

ppAction' :: (?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(I.Expr, [(String, VarAsn)])] -> Bool -> [PP.Doc]
ppAction' ((cond, lab):sol) addmb = if null sol
                                       then act
                                       else [mkITE (exprToTSL2 ?inspec ?pid ?sc cond) act (ppAction' sol addmb)]
    where
    flatspec = ?flatspec
    eact = do 
        -- extract tag
        tag <- case lookup mkTagVarName lab of
                    Just (AsnScalar [(_, Right (I.EConst (I.EnumVal tname)))]) -> return tname
                    _                                                          -> throwError $ "cannot extract tag from label assignment " ++ show lab
        -- generate method invocation
        if' (tag == mkTagDoNothing) (throwError "unexpected no-op tag") $
            if' (tag == mkTagExit) (return [PP.text "{}"]) $
            do let mpath = tagToPath tag 
                   -- method in the flat spec
                   meth  = let ?spec = flatspec in snd $ F.getMethod ?sc $ MethodRef nopos [Ident nopos tag]
                   args  = map (\a -> case argDir a of
                                           ArgIn  -> let t = let ?spec = ?flatspec 
                                                                 ?scope = ?sc
                                                             in F.argType a
                                                     in mkArg lab t $ mkArgTmpVarName meth a
                                           ArgOut -> PP.char '_') $ methArg meth
               return $ PP.text mpath PP.<> (PP.parens $ PP.hsep $ PP.punctuate PP.comma $ args) : if' addmb [PP.text "..."] []
    act = case eact of
               Left  e -> [PP.text $ "/* " ++ e ++ " */"]
               Right a -> a

mkITE :: PP.Doc -> [PP.Doc] -> [PP.Doc] -> PP.Doc
mkITE i t e = ((PP.text "if" PP.<+> PP.parens i) PP.<+> PP.char '{')
           PP.$$ (nest' $ PP.vcat $ map (PP.<> PP.semi) t)
           PP.$$ (PP.char '}' PP.<+> (PP.text "else") PP.<+> if' nestedif elcond (PP.char '{'))
           PP.$$ (if' nestedif elbody $ (nest' $ PP.vcat $ map (PP.<> PP.semi) e))
           PP.$$ (if' nestedif PP.empty (PP.char '}'))
    where eltxt = PP.render $ head e
          nestedif = length e == 1 && isPrefixOf "if (" eltxt
          elcond = PP.text $ head $ lines' eltxt
          elbody = PP.text $ unlines' $ tail $ lines' eltxt

tagToPath :: (?inspec::F.Spec, ?sc::F.Scope) => String -> String
tagToPath tag = intercalate "." $ (map sname path) ++ [mname]
    where F.ScopeMethod _ m = ?sc
          (scid, _) = itreeParseName $ sname m
          (iid, mname) = itreeParseName tag
          Just path = let ?spec = ?inspec in itreeAbsToRelPath scid iid

mkArg :: (?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(String, VarAsn)] -> F.Type -> String -> PP.Doc
mkArg lab t argname = mkArg' lab t $ I.EVar argname

mkArg' :: (?inspec::F.Spec, ?flatspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(String, VarAsn)] -> F.Type -> I.Expr -> PP.Doc
mkArg' lab t e =
    -- trace ("mkArg' " ++ show lab ++ " " ++ (show $ F.tspec t) ++ "" ++ show e) $
    case I.exprType e of
         Struct _ fs  -> let F.Type sc (F.StructSpec _ fs') = let ?spec = ?flatspec 
                                                                  ?scope = ?sc 
                                                              in F.typ' t
                         in (let ?spec = ?flatspec in F.ppType t) PP.<> 
                            (PP.braces $ PP.hcat $ PP.punctuate PP.comma $ map (\(Field n _,f) -> let t' = let ?spec = ?flatspec 
                                                                                                               ?scope = sc 
                                                                                                           in F.fieldType f
                                                                                                  in mkArg' lab t' (I.EField e n)) $ zip fs fs')
         Array _ _ _  -> error $ "mkArg " ++ show e ++ ": Arrays are not supported"
         VarArray _ _ -> error $ "mkArg " ++ show e ++ ": VarArrays are not supported"
         _            -> mkScalar lab e

mkScalar :: (?inspec::F.Spec, ?spec::Spec, ?pid::PrID, ?sc::F.Scope) => [(String, VarAsn)] -> I.Expr -> PP.Doc
mkScalar lab e | masn == Nothing = PP.text "/* any value */" PP.<> (exprToTSL2 ?inspec ?pid ?sc $ I.EConst $ I.valDefault $ I.exprType e)
               | otherwise       = PP.hcat $ PP.punctuate (PP.text " ++ ") es'
    where masn = lookupAsn e lab 
          Just (AsnScalar asns) = masn
          (off, es) = foldl' (\(o, exps) ((l,h), v) -> ((h+1), exps ++ (if' (l > o) [anyvalue (l-o)] []) ++ [ppAsn (h-l+1) v]))
                             (0, []) asns
          es' = es ++ (if' (off < I.exprWidth e) [anyvalue (I.exprWidth e - off)] [])
          ppAsn w (Left True)  = anyvalue w
          ppAsn w (Left False) = novalue w
          ppAsn _ (Right x)    = exprToTSL2 ?inspec ?pid ?sc x
          anyvalue w = PP.text $ "/*any value*/" ++ show w  ++ "'h0"
          novalue  w = PP.text $ "/*??? (" ++ show w ++ " bits)*/"
          lookupAsn (I.EField ex n) asn = maybe Nothing (\(AsnStruct a) -> lookup n a) $ lookupAsn ex asn
          lookupAsn (I.EVar n)      asn = lookup n asn

derefStep :: (RM s u t) => C.DDManager s u -> Step s u -> t (ST s) ()
derefStep m (Step (cond, care) branch) = do
    let ops@Ops{..} = constructOps m
    $d deref cond
    $d deref care
    derefBranch ops branch

derefBranch :: (RM s u t) => Ops s u -> Branch s u -> t (ST s) ()
derefBranch ops@Ops{..} (BranchITE (i,care) t e) = do
    $d deref i
    $d deref care
    $d deref t
    derefBranch ops e
derefBranch Ops{..} (BranchAction i t) = do
    $d deref i
    $d deref t
derefBranch _ (BranchStuck _)  = return ()

gen1Step :: (RM s u t) 
         => Spec 
         -> C.DDManager s u 
         -> RefineDynamic s u 
         -> DB s u AbsVar AbsVar 
         -> C.DDNode s u 
         -> Lab s u 
         -> DDNode s u 
         -> DDNode s u 
         -> DDNode s u 
         -> [DDNode s u] 
         -> t (ST s) (Step s u)
gen1Step spec m refdyn pdb cont lp set strategy goal regions = do
    let ops@Ops{..} = constructOps m
        DB{_sections=SectionInfo{..}, ..} = pdb
    let ?spec = spec
        ?m    = m
        ?db   = pdb
        ?rd   = refdyn
        ?cont = cont
        ?lp   = lp
    tagNopCond <- compileExpr (mkTagVar I.=== (I.EConst $ I.EnumVal mkTagDoNothing))
    -- Use strategy to determine states where $tagnop is a winning action
    stratinset <- $r2 band set strategy
    waitCond0 <- $r2 band stratinset tagNopCond
    $d deref stratinset
    $d deref tagNopCond
    waitCond1 <- $r1 (bexists _labelCube) waitCond0
    $d deref waitCond0
    waitCond2 <- $r1 (bexists _untrackedCube) waitCond1
    $d deref waitCond1
    waitCond  <- (liftM bnot) $ $r2 liCompact waitCond2 set
    $d deref waitCond2
    waitCond' <- condRemoveSpecialVars waitCond set
    $d deref waitCond
    $rp ref set
    let stepWaitCond = (waitCond', set)
    -- Remove these states from set
    set' <- $r2 band set waitCond'
    -- Iterate through what remains
    stepBranches <- mkBranches strategy goal regions set'
    return Step{..}

-- consumes input reference
mkBranches :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
           => DDNode s u 
           -> DDNode s u 
           -> [DDNode s u] 
           -> DDNode s u -> t (ST s) (Branch s u)
mkBranches strategy goal regions set = do
    let Ops{..} = constructOps ?m
    let RefineDynamic{..} = ?rd
    winning <- lift $ leq set (head regions)
    if winning
       then do muniqlab <- pickCommonLab strategy goal regions set
               case muniqlab of
                    Just l  -> return $ BranchAction set l
                    Nothing -> mkBranches' strategy goal regions set
       else do $d deref set
               return $ BranchStuck "state outside of the winning region"

-- consumes input reference
pickCommonLab :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
              => DDNode s u 
              -> DDNode s u 
              -> [DDNode s u] 
              -> DDNode s u -> t (ST s) (Maybe (DDNode s u))
pickCommonLab strategy goal regions set = do
    let ops@Ops{..} = constructOps ?m
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
        RefineDynamic{..} = ?rd
        sd = SynthData sinfo trans ?cont ?rd ?lp
    muniqlab <- pickLabel2 ops sd regions goal strategy set
    case muniqlab of
         Just (l, farthest) -> do itr <- CG.enumerateEquivalentLabels ops sd set l
                                  $d deref l
                                  mlab' <- pickProgressLabel farthest set itr
                                  $d deref farthest
                                  case mlab' of
                                       Nothing -> return Nothing
                                       Just l' -> return $ Just l'
         Nothing            -> return Nothing


-- Iterate through labels returned by pickLabel2 looking for one that guarantees progress
pickProgressLabel :: (RM s u t, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
                  => DDNode s u 
                  -> DDNode s u 
                  -> CG.IteratorM (t (ST s)) (DDNode s u) 
                  -> t (ST s) (Maybe (DDNode s u))
pickProgressLabel _        _   CG.Empty          = return Nothing
pickProgressLabel farthest set (CG.Item l stitr) = do
    let ops@Ops{..} = constructOps ?m
        RefineDynamic{..} = ?rd
    outerRegion <- $r2 band set farthest
    trel <- $r $ C.conj ops $ l:(map snd trans)
    suc <- let ?winregion = btrue
               ?cb = (\_ _ _ _ -> return ())
           in simulateControllable set trel
    $d deref trel
    outerRegion' <- $r2 band suc farthest
    $d deref suc
    shrinks <- lift $ leq outerRegion' outerRegion
    $d deref outerRegion
    $d deref outerRegion'
    if shrinks && outerRegion' /= outerRegion
       then return $ Just l
       else do $d deref l
               itr <- stitr
               pickProgressLabel farthest set itr
   
-- Called when none of the labels returned by pickLabel2 are sutable.
-- Uses ifCondition/pickLabel to split set into subregions.
mkBranches' :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?rd::RefineDynamic s u, ?db::DB s u AbsVar AbsVar, ?cont::C.DDNode s u, ?lp::Lab s u) 
            => DDNode s u 
            -> DDNode s u 
            -> [DDNode s u] 
            -> DDNode s u -> t (ST s) (Branch s u) 
mkBranches' strategy goal regions set = do
    let ops@Ops{..} = constructOps ?m
        DB{_sections=sinfo@SectionInfo{..}, ..} = ?db
        RefineDynamic{..} = ?rd
        sd = SynthData sinfo trans ?cont ?rd ?lp
    mcond <- ifCondition ops sd strategy set
    case mcond of
         Nothing   -> do $d deref set
                         return $ BranchStuck "no winning move found"
         Just cond -> do condset  <- $r2 band set cond
                         Just act <- pickLabel ops sd strategy condset
                         $d deref condset
                         set'     <- $r2 band set (bnot cond)
                         cond'    <- condRemoveSpecialVars cond set
                         $d deref cond
                         if set' == bfalse
                            then do $d deref set 
                                    $d deref set'
                                    return $ BranchAction cond' act
                            else do branch' <- mkBranches strategy goal regions set'
                                    return $ BranchITE (cond', set) act branch'

-- Decomposes cond into prime implicants and converts it to a boolean expression
mkCondition :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) => (DDNode s u, DDNode s u) -> t (ST s) [I.Expr]
mkCondition (cond, care) = do
    let ops@Ops{..} = constructOps ?m
    cubes_ <- lift $ C.primeCover ops cond
    cubes <- mapM ($r . return) cubes_
    res <- mapM (mkCondCube care) cubes
    mapM_ ($d deref) cubes
    return res

mkCondCube :: (RM s u t, ?spec::Spec, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) 
           => DDNode s u -> DDNode s u -> t (ST s) I.Expr
mkCondCube care cub = do
   let DB{_symbolTable = SymbolInfo{..}, ..} = ?db
   let ops@Ops{..} = constructOps ?m
   asns <- cubeToAsns ops care cub $ map (mapSnd sel2) $ M.toList _stateVars 
   return $ I.conj 
          $ map (\(av, vals) -> -- Cube may contain ivalid enum values.  Filter them out.
                                let vals' = case av of 
                                                 AVarEnum t -> let Enum _ n = termType t
                                                                   l = toInteger $ length $ enumEnums $ getEnumeration n
                                                               in filter (< l) vals
                                                 _          -> vals
                                in I.disj $ map (formToExpr . avarAsnToFormula av) vals') asns

    
cubeToAsns :: (RM s u t) => Ops s u -> DDNode s u -> DDNode s u -> [(AbsVar, [Int])] -> t (ST s) [(AbsVar, [Integer])]
cubeToAsns Ops{..} care rel vs = do
    supp <- lift $ supportIndices rel
    asn  <- lift $ satCube rel
    let supvars = filter (any (\idx -> elem idx supp) . snd) vs
    mapM (\(av, is) -> (liftM ((av,) . map boolArrToBitsBe))
                       $ filterM (\bits -> do vcubes <- mapM ($r . ithVar) is
                                              cond  <- $r $ computeCube vcubes bits
                                              mapM_ ($d deref) vcubes
                                              incare <- $r2 band cond care
                                              $d deref cond
                                              $d deref incare
                                              return $ incare /= bfalse)
                       $ sequence 
                       $ map (C.expand . (asn !!)) is)
         $ nub supvars

cubeToAsn :: (RM s u t) => Ops s u -> DDNode s u -> [(AbsVar, [Int])] -> t (ST s) [(AbsVar, [Bool])]
cubeToAsn Ops{..} rel vs = do
    supp <- lift $ supportIndices rel
    asn  <- lift $ satCube rel
    let supvars = filter (any (\idx -> elem idx supp) . snd) vs
    return $ map (\(av, is) -> (av, map (satBitToBool . (asn !!)) is))
           $ nub supvars
    where satBitToBool Zero  = False
          satBitToBool One   = True
          satBitToBool _     = False

mkLabel :: (RM s u t, ?m::C.DDManager s u, ?db::DB s u AbsVar AbsVar) => DDNode s u -> t (ST s) [(AbsVar, [Bool])]
mkLabel lab = do
    let DB{_symbolTable = SymbolInfo{..}, ..} = ?db
    let ops@Ops{..} = constructOps ?m
    lab' <- $r $ C.largePrime ops lab
    asn  <- lift $ satCube lab'
    let enabledvars = filter ((\enidx -> (asn !! enidx) == One)  . sel4 . snd)
                      $ M.toList _labelVars
    res <- cubeToAsn ops lab' $ map (mapSnd sel2) enabledvars
    $d deref lab'
    return res
