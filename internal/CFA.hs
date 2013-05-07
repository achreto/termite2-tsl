{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ImplicitParams #-}

module CFA(Statement(..),
           Frame(..),
           frameMethod,
           Stack,
           showStack,
           (=:),
           Loc,
           LocAction(..),
           LocLabel(..),
           TranLabel(..),
           CFA,
           isDelayLabel,
           newCFA,
           cfaNop,
           cfaErrLoc,
           cfaErrVarName,
           cfaInitLoc,
           cfaDelayLocs,
           cfaInsLoc,
           cfaLocLabel,
           cfaLocSetAct,
           cfaLocSetStack,
           cfaInsTrans,
           cfaInsTransMany,
           cfaInsTrans',
           cfaInsTransMany',
           cfaErrTrans,
           cfaSuc,
           cfaFinal,
           cfaAddNullPtrTrans,
           cfaAddNullTypes,
           cfaPruneUnreachable,
           cfaReachInst,
           cfaPrune,
           cfaTrace,
           cfaTraceFile,
           cfaTraceFileMany,
           cfaShow,
           cfaSave) where

import qualified Data.Graph.Inductive.Graph    as G
import qualified Data.Graph.Inductive.Tree     as G
import qualified Data.Graph.Inductive.Graphviz as G
import Data.Maybe
import Data.List
import Data.Tuple
import qualified Data.Set as S
import Text.PrettyPrint
import System.IO.Unsafe
import System.Process
import Data.String.Utils

import Name
import PP
import Ops
import Util hiding (name,trace)
import IExpr
import IType
import {-# SOURCE #-} ISpec

-- Frontend imports
import qualified NS        as F
import qualified Statement as F
import qualified Expr      as F
import qualified Method    as F

-- Atomic statement
data Statement = SAssume Expr
               | SAssign Expr Expr
               deriving (Eq)

instance PP Statement where
    pp (SAssume e)   = text "assume" <+> (parens $ pp e)
    pp (SAssign l r) = pp l <+> text ":=" <+> pp r

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

instance PP LocAction where
    pp (ActStat s) = pp s
    pp (ActExpr e) = pp e
    pp ActNone     = empty

-- Stack frame
data Frame = FrameStatic      {fScope :: F.Scope, fLoc :: Loc}
           | FrameInteractive {fScope :: F.Scope, fLoc :: Loc, fCFA :: CFA}

instance PP Frame where
    pp (FrameStatic      sc loc  ) =                         text (show sc) <> char ':' <+> pp loc
    pp (FrameInteractive sc loc _) = text "interactive:" <+> text (show sc) <> char ':' <+> pp loc

frameMethod :: Frame -> Maybe F.Method
frameMethod f = case fScope f of
                     F.ScopeMethod _ m -> Just m
                     _                 -> Nothing

type Stack = [Frame]

instance PP Stack where
    pp stack = vcat $ map pp stack

showStack :: Stack -> String
showStack = render . pp

data LocLabel = LInst  {locAct :: LocAction}
              | LPause {locAct :: LocAction, locStack :: Stack, locExpr :: Expr}
              | LFinal {locAct :: LocAction, locStack :: Stack}

instance PP LocLabel where
    pp (LInst  a)     = pp a
    pp (LPause a _ e) = text "wait" <> (parens $ pp e) $$ pp a
    pp (LFinal a _)   = text "F"                       $$ pp a

instance Show LocLabel where
    show = render . pp

data TranLabel = TranCall F.Method
               | TranReturn
               | TranNop
               | TranStat Statement

instance Eq TranLabel where
    (==) (TranCall m1) (TranCall m2) = sname m1 == sname m2
    (==) TranReturn    TranReturn    = True
    (==) TranNop       TranNop       = True
    (==) (TranStat s1) (TranStat s2) = s1 == s2
    (==) _             _             =  False

instance PP TranLabel where
    pp (TranCall m)  = text "call" <+> text (sname m)
    pp TranReturn    = text "return"
    pp TranNop       = text ""
    pp (TranStat st) = pp st

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

instance Show CFA where
    show = render . pp

cfaTrace :: CFA -> String -> a -> a
cfaTrace cfa title x = unsafePerformIO $ do
    cfaShow cfa title
    return x

sanitize :: String -> String
sanitize title = replace "\"" "_" $ replace "/" "_" $ replace "$" "" $ replace ":" "_" title

cfaTraceFile :: CFA -> String -> a -> a
cfaTraceFile cfa title x = unsafePerformIO $ do
    _ <- cfaSave cfa title False
    return x

cfaTraceFileMany :: [CFA] -> String -> a -> a
cfaTraceFileMany cfas title x = unsafePerformIO $ do
    fnames <- mapM (\(cfa,n) -> cfaSave cfa (title++show n) True) $ zip cfas ([1..]::[Int])
    _ <- readProcess "psmerge" (["-o" ++ (sanitize title) ++ ".ps"]++fnames) ""
    return x

cfaShow :: CFA -> String -> IO ()
cfaShow cfa title = do
    fname <- cfaSave cfa title True
    _ <- readProcess "evince" [fname] ""
    return ()

cfaSave :: CFA -> String -> Bool -> IO String
cfaSave cfa title tmp = do
    let -- Convert graph to dot format
        title' = sanitize title
        fname = (if tmp then "/tmp/" else "") ++ "cfa_" ++ title' ++ ".ps"
        graphstr = cfaToDot cfa title'
    writeFile (fname++".dot") graphstr
    _ <- readProcess "dot" ["-Tps", "-o" ++ fname] graphstr 
    return fname

cfaToDot :: CFA -> String -> String
cfaToDot cfa title = G.graphviz cfa' title (6.0, 11.0) (1,1) G.Portrait
    where cfa' = G.emap (eformat . show)
                 $ G.gmap (\(inb, n, l, outb) -> (inb, n, show n ++ ": " ++ (nformat $ show l), outb)) cfa
          maxLabel = 64
          nformat :: String -> String
          nformat s = if' (length s <= maxLabel) s ((take maxLabel s) ++ "...") 
          eformat :: String -> String
          eformat s | length s <= maxLabel = s
                    | otherwise            =
                        (take maxLabel s) ++ "\n" ++ eformat (drop maxLabel s)

isDelayLabel :: LocLabel -> Bool
isDelayLabel (LPause _ _ _) = True
isDelayLabel (LFinal _ _)   = True
isDelayLabel (LInst _)      = False



newCFA :: F.Scope -> F.Statement -> Expr -> CFA 
newCFA sc stat initcond = G.insNode (cfaInitLoc,LPause (ActStat stat) [FrameStatic sc cfaInitLoc] initcond) 
                        $ G.insNode (cfaErrLoc,LPause ActNone [FrameStatic sc cfaErrLoc] false) G.empty

cfaErrLoc :: Loc
cfaErrLoc = 0

cfaErrVarName :: String
cfaErrVarName = "$err"

cfaInitLoc :: Loc
cfaInitLoc = 1

cfaNop :: CFA
cfaNop = cfaInsTrans cfaInitLoc fin TranNop cfa
    where (cfa, fin) = cfaInsLoc (LFinal ActNone [])
                       $ G.insNode (cfaInitLoc,LInst ActNone) G.empty

cfaDelayLocs :: CFA -> [Loc]
cfaDelayLocs = map fst . filter (isDelayLabel . snd) . G.labNodes

cfaInsLoc :: LocLabel -> CFA -> (CFA, Loc)
cfaInsLoc lab cfa = (G.insNode (loc,lab) cfa, loc)
   where loc = (snd $ G.nodeRange cfa) + 1

cfaLocLabel :: Loc -> CFA -> LocLabel
cfaLocLabel loc cfa = fromJustMsg "cfaLocLabel" $ G.lab cfa loc

cfaLocSetAct :: Loc -> LocAction -> CFA -> CFA
cfaLocSetAct loc act cfa = G.gmap (\(to, lid, n, from) -> 
                                    (to, lid, if lid == loc then n {locAct = act} else n, from)) cfa


cfaLocSetStack :: Loc -> Stack -> CFA -> CFA
cfaLocSetStack loc stack cfa = G.gmap (\(to, lid, n, from) -> 
                                      (to, lid, if lid == loc then n {locStack = stack} else n, from)) cfa


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

cfaErrTrans :: Loc -> TranLabel -> CFA -> CFA
cfaErrTrans loc stat cfa =
    let (cfa',loc') = cfaInsTrans' loc stat cfa
    in cfaInsTrans loc' cfaErrLoc (TranStat $ EVar cfaErrVarName =: true) cfa'

cfaSuc :: Loc -> CFA -> [(TranLabel,Loc)]
cfaSuc loc cfa = map swap $ G.lsuc cfa loc

cfaFinal :: CFA -> [Loc]
cfaFinal cfa = map fst $ filter (\n -> case snd n of
                                            LFinal _ _ -> True
                                            _          -> False) $ G.labNodes cfa

-- Add error transitions for all potential null-pointer dereferences
cfaAddNullPtrTrans :: CFA -> CFA
cfaAddNullPtrTrans cfa = foldl' addNullPtrTrans1 cfa (G.labEdges cfa)

addNullPtrTrans1 :: CFA -> (Loc,Loc,TranLabel) -> CFA
addNullPtrTrans1 cfa (from , to, l@(TranStat (SAssign e1 e2))) = 
    case cond of
         EConst (BoolVal False) -> cfa
         _ -> let (cfa1, from') = cfaInsLoc (LInst ActNone) cfa
                  cfa2 = cfaInsTrans from' to l $ G.delLEdge (from, to, l) cfa1
                  cfa3 = cfaInsTrans from from' (TranStat $ SAssume $ neg cond) cfa2
              in cfaErrTrans from (TranStat $ SAssume cond) cfa3
    where cond = -- We don't have access to ?spec here, hence cannot determine type of
                 -- NullVal.  Keep it undefined until a separate pass.
                 disj 
                 $ map (\e -> e === (EConst $ NullVal $ error "NullVal type undefined")) 
                 $ exprPtrSubexpr e1 ++ exprPtrSubexpr e2
    
addNullPtrTrans1 cfa (_    , _, _)                             = cfa

-- Add types to NullVal expressions introduced by cfaAddNullPtrTrans
cfaAddNullTypes :: Spec -> CFA -> CFA
cfaAddNullTypes spec cfa = G.emap (\l -> case l of 
                                              TranStat st -> TranStat $ (statAddNullTypes spec) st
                                              _           -> l) cfa

statAddNullTypes :: Spec -> Statement -> Statement
statAddNullTypes spec (SAssume (EBinOp Eq e (EConst (NullVal _)))) = let ?spec = spec in
                                                                     SAssume (EBinOp Eq e (EConst $ NullVal $ typ e))
statAddNullTypes _    s = s


cfaPruneUnreachable :: CFA -> [Loc] -> CFA
cfaPruneUnreachable cfa keep = 
    let unreach = filter (\n -> (not $ elem n keep) && (null $ G.pre cfa n)) $ G.nodes cfa
    in if null unreach 
          then cfa
          else --trace ("cfaPruneUnreachable: " ++ show cfa ++ "\n"++ show unreach) $
               cfaPruneUnreachable (foldl' (\_cfa n -> G.delNode n _cfa) cfa unreach) keep

-- locations reachable from specified location before reaching the next delay location
-- (the from location if not included in the result)
cfaReachInst :: CFA -> Loc -> S.Set Loc
cfaReachInst cfa from = cfaReachInst' cfa S.empty (S.singleton from)

cfaReachInst' :: CFA -> S.Set Loc -> S.Set Loc -> S.Set Loc
cfaReachInst' cfa found frontier = if S.null frontier'
                                     then found'
                                     else cfaReachInst' cfa found' frontier'
    where new       = suc frontier
          found'    = S.union found new
          -- frontier' - all newly discovered states that are not pause or final states
          frontier' = S.filter (not . isDelayLabel . fromJust . G.lab cfa) $ new S.\\ found
          suc locs  = S.unions $ map suc1 (S.toList locs)
          suc1 loc  = S.fromList $ G.suc cfa loc

-- Prune CFA, leaving only specified subset of locations
cfaPrune :: CFA -> S.Set Loc -> CFA
cfaPrune cfa locs = foldl' (\g l -> if S.member l locs then g else G.delNode l g) cfa (G.nodes cfa)

