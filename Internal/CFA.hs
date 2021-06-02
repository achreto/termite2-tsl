{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ImplicitParams #-}

module Internal.CFA(Statement(..),
           Frame(..),
           frameMethod,
           Stack,
           stackSetLoc,
           (=:),
           Loc,
           LocAction(..),
           isActNone,
           LocLabel(..),
           TranLabel(..),
           CFA,
           isDelayLabel,
           isDeadendLoc,
           isMBLabel,
           isMBLoc,
           cfaFindMBs,
           cfaFindMBAtPos,
           newCFA,
           cfaNop,
           cfaErrVarName,
           cfaInitLoc,
           cfaDelayLocs,
           cfaInsLoc,
           cfaLocLabel,
           cfaLocPos,
           cfaFindLabel,
           cfaLocSetAct,
           cfaLocSetStack,
           cfaLocInline,
           cfaLocWaitCond,
           cfaInsTrans,
           cfaInsTransMany,
           cfaInsTrans',
           cfaInsTransMany',
           cfaErrTrans,
           cfaSuc,
           cfaFinal,
           cfaPruneUnreachable,
           cfaReachInst,
           cfaPrune,
           cfaMapStat,
           cfaMapExpr,
           cfaTrace,
           cfaTraceFile,
           cfaTraceFileMany,
           cfaShow,
           cfaSave,
           cfaSplitLoc,
           cfaLocTrans,
           cfaLocTransCFA,
           cfaSource,
           cfaSink) where

import Prelude hiding ((<>))
import qualified Data.Graph.Inductive as G
import Data.Maybe
import Data.List
import Data.Tuple
import qualified Data.Set             as S
import qualified Data.Map             as M
import Text.PrettyPrint
import qualified Text.Parsec          as P

import Pos
import Name
import PP
import Util hiding (name)
import TSLUtil
import Internal.IExpr

-- Frontend imports
import qualified Frontend.NS        as F
import qualified Frontend.Statement as F
import qualified Frontend.Expr      as F
import qualified Frontend.Method    as F

-- Atomic statement
data Statement = SAssume  Expr
               | SAssert  Expr   -- in transducers only
               | SAssign  Expr Expr
               | SOut     Expr Expr
               deriving (Eq)

instance PP Statement where
    pp (SAssume e)   = text "assume" <+> (parens $ pp e)
    pp (SAssert e)   = text "assert" <+> (parens $ pp e)
    pp (SAssign l r) = pp l <+> text ":=" <+> pp r
    pp (SOut l r)    = pp l <+> text ">>" <+> pp r

instance Show Statement where
    show = render . pp

(=:) :: Expr -> Expr -> Statement
(=:) e1 e2 = SAssign e1 e2

------------------------------------------------------------
-- Control-flow automaton
------------------------------------------------------------

type Loc = G.Node

-- Syntactic element associated with CFA location
data LocAction = ActStat F.Statement
               | ActExpr F.Expr
               | ActNone

isActNone :: LocAction -> Bool
isActNone ActNone = True
isActNone _       = False

instance PP LocAction where
    pp (ActStat s) = pp s
    pp (ActExpr e) = pp e
    pp ActNone     = empty

instance Show LocAction where
    show = render . pp

instance WithPos LocAction where
    pos (ActStat s) = pos s
    pos (ActExpr e) = pos e
    atPos _ _ = error "LocAction::atPos not implemented"


-- Stack frame
data Frame = Frame { fScope :: F.Scope
                   , fLoc   :: Loc}

instance PP Frame where
    pp (Frame sc loc) = text (show sc) <> char ':' <+> pp loc

frameMethod :: Frame -> Maybe F.Method
frameMethod f = case fScope f of
                     F.ScopeMethod _ m -> Just m
                     _                 -> Nothing

type Stack = [Frame]

instance PP Stack where
    pp stack = vcat $ map pp stack

stackSetLoc :: Stack -> Loc -> Stack
stackSetLoc ((Frame sc _):frs) l' = (Frame sc l') : frs

data LocLabel = LInst    {locAct :: LocAction}
              | LPause   {locAct :: LocAction, locStack :: Stack, locLabels :: [String], locExpr :: Expr}
              | LIn      {locAct :: LocAction, locLHS :: Expr, locRHS :: Expr}
              | LFinal   {locAct :: LocAction, locStack :: Stack, locLabels :: [String]}

instance PP LocLabel where
    pp (LInst  a)          = pp a
    pp (LPause a _ labs e) = text "WAIT" <> (brackets $ hcat $ punctuate comma $ map pp labs) <> (parens $ pp e) $$ pp a
    pp (LIn a l r)         = pp l <+> pp "<<" <+> pp r                                                           $$ pp a
    pp (LFinal a _ labs)   = text "F"    <> (brackets $ hcat $ punctuate comma $ map pp labs)                    $$ pp a

instance Show LocLabel where
    show = render . pp

data TranLabel = TranCall F.Method Loc -- method and return location
               | TranReturn
               | TranNop
               | TranStat Statement

instance Eq TranLabel where
    (==) (TranCall m1 l1) (TranCall m2 l2) = sname m1 == sname m2 && l1 == l2
    (==) TranReturn       TranReturn       = True
    (==) TranNop          TranNop          = True
    (==) (TranStat s1)    (TranStat s2)    = s1 == s2
    (==) _                _                = False

instance PP TranLabel where
    pp (TranCall m l) = text "call" <+> text (sname m) <+> text "retloc=" <> pp l
    pp TranReturn     = text "return"
    pp TranNop        = text ""
    pp (TranStat st)  = pp st

instance Show TranLabel where
    show = render . pp

type CFA = G.Gr LocLabel TranLabel

instance PP CFA where
    pp cfa = text "states:"
             $+$
             (vcat $ map (\(loc,lab) -> pp loc <> char ':' <+> pp lab) $ G.labNodes cfa)
             $+$
             text "transitions:"
             $+$
             (vcat $ map (\(from,to,s) -> pp from <+> text "-->" <+> pp to <> char ':' <+> pp s) $ G.labEdges cfa)

--instance Show CFA where
--    show = render . pp

cfaTrace :: CFA -> String -> a -> a
cfaTrace cfa title x = graphTrace cfa title x

cfaTraceFile :: CFA -> String -> a -> a
cfaTraceFile cfa title x = graphTraceFile cfa title x

cfaTraceFileMany :: [CFA] -> String -> a -> a
cfaTraceFileMany cfas title x = graphTraceFileMany cfas title x

cfaShow :: CFA -> String -> IO ()
cfaShow cfa title = graphShow cfa title

cfaSave :: CFA -> String -> Bool -> IO String
cfaSave cfa title tmp = graphSave cfa ("cfa_" ++ title) tmp

isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _ _ _ _) = True
isDelayLabel (LFinal _ _ _)   = True
isDelayLabel (LIn _ _ _)      = True
isDelayLabel (LInst _)        = False

isDeadendLoc :: CFA -> Loc -> Bool
isDeadendLoc cfa loc = G.outdeg cfa loc == 0

isMBLabel :: LocLabel -> Bool
isMBLabel lab = isDelayLabel lab && 
                         case locAct lab of
                              ActStat (F.SMagic _ _) -> True
                              _                      -> False

isMBLoc :: CFA -> Loc -> Bool
isMBLoc cfa loc = isMBLabel $ cfaLocLabel loc cfa

cfaFindMBs :: CFA -> [Loc]
cfaFindMBs cfa = nub 
                 $ filter (\l -> case locAct $ cfaLocLabel l cfa of
                                      ActStat (F.SMagic _ _) -> True
                                      _                      -> False)
                 $ cfaDelayLocs cfa

cfaFindMBAtPos :: CFA -> P.SourcePos -> Maybe Loc
cfaFindMBAtPos cfa sp = find (\l -> case locAct $ cfaLocLabel l cfa of
                                         ActStat (F.SMagic p _) -> posInside sp p
                                         _                      -> False)
                     $ cfaDelayLocs cfa

cfaLocWaitCond :: CFA -> Loc -> Expr
cfaLocWaitCond cfa loc = case cfaLocLabel loc cfa of
                              LPause _ _ _ c -> c
                              LFinal _ _ _   -> true

cfaLocPos :: CFA -> Loc -> Pos
cfaLocPos cfa loc = pos $ locAct $ cfaLocLabel loc cfa

newCFA :: F.Scope -> F.Statement -> Expr -> CFA 
newCFA sc stat initcond = G.insNode (cfaInitLoc,LPause (ActStat stat) [Frame sc cfaInitLoc] [] initcond) G.empty

cfaErrVarName :: String
cfaErrVarName = "$err"

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaNop :: CFA
cfaNop = cfaInsTrans cfaInitLoc fin TranNop cfa
    where (cfa, fin) = cfaInsLoc (LFinal ActNone [] [])
                       $ G.insNode (cfaInitLoc,LInst ActNone) G.empty

cfaDelayLocs :: CFA -> [Loc]
cfaDelayLocs = map fst . filter (isDelayLabel . snd) . G.labNodes

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaLocLabel :: Loc -> CFA -> LocLabel
cfaLocLabel loc cfa = fromJust $ G.lab cfa loc

cfaFindLabel :: CFA -> String -> [Loc]
cfaFindLabel cfa lab = filter (\loc -> elem lab $ locLabels $ cfaLocLabel loc cfa) 
                       $ cfaDelayLocs cfa

cfaLocSetAct :: Loc -> LocAction -> CFA -> CFA
cfaLocSetAct loc act cfa = graphUpdNode loc (\n -> n {locAct = act}) cfa 
          
cfaLocSetStack :: Loc -> Stack -> CFA -> CFA
cfaLocSetStack loc stack cfa = graphUpdNode loc (\n -> n {locStack = stack}) cfa

cfaLocInline :: CFA -> Loc -> CFA -> CFA
cfaLocInline cfa loc inscfa = inlineBetween cfa2 loc loc' inscfa
    -- Replicate location.  The new location is not a delay location
    -- and contains all outgoing transitions of the original location
    where (cfa1, loc') = cfaInsLoc (LInst $ locAct $ cfaLocLabel loc cfa) cfa
          cfa2 = foldl' (\cfa' (toloc, lab) -> G.delLEdge (loc, toloc, lab) 
                                               $ cfaInsTrans loc' toloc lab cfa')
                        cfa1 (G.lsuc cfa loc)

inlineBetween :: CFA -> Loc -> Loc -> CFA -> CFA
inlineBetween cfa0 bef aft inscfa = 
    let -- for each node in inscfa, create a replica in CFA and store
        -- correspondence in a table
        (cfa1, locs1) = foldl' (\(cfa,locs) loc -> let lab = cfaLocLabel loc inscfa
                                                       (cfa', loc') = cfaInsLoc (LInst $ locAct lab) cfa
                                                   in if' (loc == cfaInitLoc)       (cfaInsTrans bef loc' TranNop cfa', locs ++ [loc']) $
                                                      if' (null $ G.suc inscfa loc) (cfa, locs ++ [aft]) $
                                                      (cfa', locs++[loc']))
                               (cfa0,[]) (G.nodes inscfa)
        match = M.fromList $ zip (G.nodes inscfa) locs1
    in -- copy transitions over
       foldl' (\cfa (from, to, l) -> cfaInsTrans (match M.! from) (match M.! to) l cfa) cfa1 (G.labEdges inscfa)

cfaInsTrans :: Loc -> Loc -> TranLabel -> CFA -> CFA
cfaInsTrans from to stat cfa = G.insEdge (from,to,stat) cfa

cfaInsTransMany :: Loc -> Loc -> [TranLabel] -> CFA -> CFA
cfaInsTransMany from to [] cfa = cfaInsTrans from to TranNop cfa
cfaInsTransMany from to stats cfa = cfaInsTrans aft to (last stats) cfa'
    where (cfa', aft) = foldl' (\(_cfa, loc) stat -> cfaInsTrans' loc stat _cfa) 
                               (cfa, from) (init stats)

cfaInsTrans' :: Loc -> TranLabel -> CFA -> (CFA, Loc)
cfaInsTrans' from stat cfa = (cfaInsTrans from to stat cfa', to)
    where (cfa', to) = cfaInsLoc (LInst ActNone) cfa

cfaInsTransMany' :: Loc -> [TranLabel] -> CFA -> (CFA, Loc)
cfaInsTransMany' from stats cfa = (cfaInsTransMany from to stats cfa', to)
    where (cfa', to) = cfaInsLoc (LInst ActNone) cfa

cfaErrTrans :: Loc -> Loc -> CFA -> CFA
cfaErrTrans from to cfa = cfaInsTrans from to (TranStat $ EVar cfaErrVarName =: true) cfa

cfaSuc :: Loc -> CFA -> [(TranLabel,Loc)]
cfaSuc loc cfa = map swap $ G.lsuc cfa loc

cfaFinal :: CFA -> [Loc]
cfaFinal cfa = map fst $ filter (\n -> case snd n of
                                            LFinal _ _ _ -> True
                                            _            -> False) $ G.labNodes cfa

cfaPruneUnreachable :: CFA -> [Loc] -> CFA
cfaPruneUnreachable cfa keep = 
    let unreach = filter (\n -> (not $ elem n keep) && (null $ G.pre cfa n)) $ G.nodes cfa
    in if null unreach 
          then cfa
          else --trace ("cfaPruneUnreachable: " ++ show cfa ++ "\n"++ show unreach) $
               cfaPruneUnreachable (foldl' (\_cfa n -> G.delNode n _cfa) cfa unreach) keep

-- locations reachable from specified location before reaching the next delay location
-- (the from location is not included in the result)
cfaReachInst :: CFA -> (Loc->Bool) -> Loc -> S.Set Loc
cfaReachInst cfa isdelay from = cfaReachInst' cfa isdelay S.empty (S.singleton from)

cfaReachInst' :: CFA -> (Loc->Bool) -> S.Set Loc -> S.Set Loc -> S.Set Loc
cfaReachInst' cfa isdelay found frontier = if S.null frontier'
                                     then found'
                                     else cfaReachInst' cfa isdelay found' frontier'
    where new       = suc frontier
          found'    = S.union found new
          -- frontier' - all newly discovered states that are not pause or final states
          frontier' = S.filter (not . isdelay) $ new S.\\ found
          suc locs  = S.unions $ map suc1 (S.toList locs)
          suc1 loc  = S.fromList $ G.suc cfa loc

-- Prune CFA, leaving only specified subset of locations
cfaPrune :: CFA -> S.Set Loc -> CFA
cfaPrune cfa locs = foldl' (\g l -> if S.member l locs then g else G.delNode l g) cfa (G.nodes cfa)


cfaMapStat :: CFA -> (Statement -> Statement) -> CFA
cfaMapStat cfa f = G.emap (\l -> case l of 
                                      TranStat st -> TranStat $ f st
                                      _           -> l) cfa

cfaMapExpr :: CFA -> (Expr -> Expr) -> CFA
cfaMapExpr cfa f = cfaMapStat cfa f'
    where f' (SAssume e)   = SAssume $ f e
          f' (SAssert e)   = SAssert $ f e
          f' (SAssign l r) = SAssign (f l) (f r)

-- Split location into 2, one containing all outgoing edges and one containing
-- all incoming edges of the original location
cfaSplitLoc :: Loc -> CFA -> (Loc, CFA)
cfaSplitLoc loc cfa = (loc', cfa3)
    where i            = G.inn cfa loc
          cfa1         = foldl' (\cfa0 (f,t,_) -> G.delEdge (f,t) cfa0) cfa i 
          (cfa2, loc') = cfaInsLoc (LInst ActNone) cfa1
          cfa3         = foldl' (\cfa0 (f,_,l) -> G.insEdge (f,loc',l) cfa0) cfa2 i

cfaLocTransCFA :: CFA -> [Loc] -> Loc -> CFA
cfaLocTransCFA cfa locs loc = cfa''
    where r = cfaReachInst cfa ((flip elem) locs) loc
          dsts = filter ((flip elem) locs) $ S.toList r 
          cfa' = cfaPrune cfa (S.insert loc r)
          cfa'' = foldl' (\cfa0 (f,t,_) -> G.delEdge (f,t) cfa0) cfa' $ concatMap (G.out cfa') dsts
          cfa''' = if null $ G.pre cfa'' loc
                      then cfa''
                      else snd $ cfaSplitLoc loc cfa''

-- Atomic transitions originating from location
-- Each returned CFA has a single source and a single sink location.
cfaLocTrans :: CFA -> Loc -> [(Loc, CFA)]
cfaLocTrans cfa loc =
    let -- compute all reachable locations before pause
        isdelay = isDelayLabel . fromJust . G.lab cfa
        r = cfaReachInst cfa isdelay loc
        -- construct subgraph with only these nodes
        cfa' = cfaPrune cfa (S.insert loc r)
        -- (This is a good place to check for loop freedom.)
        -- for each final location, compute a subgraph that connects the two
        dsts = filter isdelay $ S.toList r 
    in map (\dst -> let cfa'' = pruneTrans cfa' loc dst in
                    if' (dst == loc) (dst, snd $ cfaSplitLoc loc cfa'') (dst, cfa'')) 
           dsts

-- Source location (without incoming edges)
cfaSource :: CFA -> [Loc]
cfaSource cfa = filter (null . G.pre cfa) $ G.nodes cfa

-- Sink locations (without outgoing edges)
cfaSink :: CFA -> [Loc]
cfaSink cfa = filter (null . G.suc cfa) $ G.nodes cfa

-- iteratively prune dead-end locations until only transitions connecting from and to remain
pruneTrans :: CFA -> Loc -> Loc -> CFA
pruneTrans cfa from to = if G.noNodes cfa'' == G.noNodes cfa then cfa'' else pruneTrans cfa'' from to
    where -- eliminate from-->from loops and to-->... transitions, unless we are generating a loop transition
          cfa' = if from /= to
                    then foldl' (\cfa0 (f,t,_) -> G.delEdge (f,t) cfa0) cfa $ G.inn cfa from ++ G.out cfa to
                    else cfa
          cfa'' = foldl' (\g loc -> if loc /= to && null (G.suc g loc) then G.delNode loc g else g) cfa' (G.nodes cfa') 
