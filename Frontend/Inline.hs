{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Frontend.Inline where

import Data.List
import Data.List.Split
import Data.Maybe
import Data.Tuple.Select
import Control.Monad.State
import Text.PrettyPrint
import qualified Data.Map             as M
import qualified Data.Graph.Inductive as G

import Util hiding (name)
import PP
import qualified Internal.IExpr    as I
import qualified Internal.CFA      as I
import qualified Internal.IType    as I
import qualified Internal.IVar     as I
import qualified Internal.ISpec    as I
import Internal.PID
import Name
import Frontend.NS
import Frontend.Method
import Frontend.Spec
import Frontend.Template
import Frontend.Process
import Frontend.Type
import Frontend.TypeOps
import Frontend.ExprOps
import Frontend.Transducer
import Frontend.Statement
import Ops
import Frontend.Const
import Frontend.Val

-- Extract template from flattened spec (that only has one template)
tmMain :: (?spec::Spec) => Template
tmMain = head $ specTemplate ?spec

----------------------------------------------------------------------
-- Names
----------------------------------------------------------------------

mkVarName :: (WithName a) => NSID -> a -> String
mkVarName nsid x = mkVarNameS nsid (sname x)

mkVarNameS :: NSID -> String -> String
mkVarNameS (NSID mpid mmeth) s = intercalate "/" names
    where -- don't prefix function, procedure, and controllable task variables with PID
          mpid' = case mmeth of
                       Nothing -> mpid
                       Just m  -> case methCat m of
                                       Function          -> Nothing
                                       Procedure         -> Nothing
                                       Task Controllable -> Nothing
                                       _                 -> mpid
          names = maybe [] (return . show)              mpid' ++ 
                  maybe [] (return . (++ "()") . sname) mmeth ++ 
                  [s]

mkVar :: (WithName a) => NSID -> a -> I.Expr
mkVar nsid x = I.EVar $ mkVarName nsid x

mkVarS :: NSID -> String -> I.Expr
mkVarS nsid s = I.EVar $ mkVarNameS nsid s

mkVarDecl :: (?spec::Spec, WithName a) => Bool -> NSID -> a -> Type -> I.Var
mkVarDecl mem nsid n t = I.Var mem I.VarState (mkVarName nsid n) (mkType t)

parseVarName :: String -> (Maybe PrID, Maybe String, String)
parseVarName n = (mpid, mmeth, vname)
    where toks = splitOn "/" n
          vname = last toks
          (mpid,mmeth) = case init toks of
                              []    -> (Nothing, Nothing)
                              toks' -> (mp, mm)
                                       where
                                       mm = if (take 2 $ reverse $ last toks') == ")("
                                               then Just $ init $ init $ last toks'
                                               else Nothing
                                       mp = case init toks' of
                                                 []     -> Nothing
                                                 (p:ps) -> Just $ PrID p ps

-- Variable that stores return value of a task
mkRetVar :: Maybe PrID -> Method -> Maybe I.Expr
mkRetVar mpid meth = case methRettyp meth of
                          Nothing -> Nothing
                          Just _  -> Just $ mkVarS (NSID mpid (Just meth)) "$ret"

mkRetVarDecl :: (?spec::Spec) => Maybe PrID -> Method -> Maybe I.Var
mkRetVarDecl mpid meth = case methRettyp meth of
                              Nothing -> Nothing
                              Just t  -> Just $ I.Var False
                                                      I.VarState
                                                      (mkVarNameS (NSID mpid (Just meth)) "$ret") 
                                                      (mkType $ Type (ScopeTemplate tmMain) t)

mkEnVarName :: PrID -> Maybe Method -> String
mkEnVarName pid mmeth = mkVarNameS (NSID (Just pid) mmeth) "$en"

mkEnVar :: PrID -> Maybe Method -> I.Expr
mkEnVar pid mmeth = I.EVar $ mkEnVarName pid mmeth

mkEnVarDecl :: PrID -> Maybe Method -> I.Var
mkEnVarDecl pid mmeth = I.Var False I.VarState (mkEnVarName pid mmeth) (I.Bool Nothing)

mkWaitForTask :: PrID -> Method -> I.Expr
mkWaitForTask pid meth = envar I.=== I.false
    where envar = mkEnVar pid (Just meth)

isWaitForTask :: I.Expr -> Maybe String
isWaitForTask (I.EBinOp Eq (I.EVar n) e2) | e2 == I.false = 
    case parseVarName n of
         (_, ms, "$en") -> ms
         _              -> Nothing
isWaitForTask _ = Nothing

isWaitForMagic :: I.Expr -> Bool
isWaitForMagic (I.EBinOp Eq (I.EVar n) e2) | (e2 == I.false) && (n == mkMagicVarName) = True
                                           | otherwise = False
isWaitForMagic _ = False

mkPCVarName :: PrID -> String
mkPCVarName pid = mkVarNameS (NSID (Just pid) Nothing) "$pc"

mkPCEnumName :: PrID -> String
mkPCEnumName pid = mkVarNameS (NSID (Just pid) Nothing) "$pcenum"

--mkPCVar :: PrID -> I.Expr
--mkPCVar pid = I.EVar $ mkPCVarName pid

mkPCEnum :: PrID -> I.Loc -> String
mkPCEnum pid loc = mkVarNameS (NSID (Just pid) Nothing) $ "$pc" ++ show loc

mkPC :: PrID -> I.Loc -> I.Expr
mkPC pid loc = I.EConst $ I.EnumVal $ mkPCEnum pid loc 

mkPCEq :: I.CFA -> PrID -> I.Expr -> I.Expr
mkPCEq cfa pid e | (length $ I.cfaDelayLocs cfa) <= 1 = I.true
                 | otherwise                          = (I.EVar $ mkPCVarName pid) I.=== e

mkPCAsn :: I.CFA -> PrID -> I.Expr -> I.TranLabel
mkPCAsn cfa pid e | (length $ I.cfaDelayLocs cfa) <= 1 = I.TranNop
                  | otherwise                          = I.TranStat $ (I.EVar $ mkPCVarName pid) I.=: e

pcEnumToLoc :: String -> I.Loc
pcEnumToLoc str = read 
                  $ drop (length "$pc") 
                  $ fromJust $ find (isPrefixOf "$pc")
                  $ reverse 
                  $ tails str

-- Variables that encode fairness

mkFairSchedVarName :: String
mkFairSchedVarName = "$fair_sched"

mkFairSchedVarDecl :: I.Var
mkFairSchedVarDecl = I.Var False I.VarState mkFairSchedVarName (I.Bool Nothing)

mkFairSchedVar :: I.Expr
mkFairSchedVar = I.EVar mkFairSchedVarName

mkFairProcVarName :: PrID -> String
mkFairProcVarName pid = "$pfair_" ++ show pid

fairProcVarPID :: String -> Maybe PrID
fairProcVarPID s | isPrefixOf "$pfair_" s = Just $ parsePID $ drop (length "$pfair_") s
                 | otherwise              = Nothing

isFairVarName :: String -> Bool
isFairVarName n = (isJust $ fairProcVarPID n) || n == mkFairSchedVarName

mkFairProcVarDecl :: PrID -> I.Var
mkFairProcVarDecl pid = I.Var False I.VarState (mkFairProcVarName pid) (I.Bool Nothing)

mkFairProcVar :: PrID -> I.Expr
mkFairProcVar pid = I.EVar $ mkFairProcVarName pid

mkFairRegVarDecls :: I.Spec -> [I.Var]
mkFairRegVarDecls spec = mkFairSchedVarDecl : (map (mkFairProcVarDecl . fst) $ I.specAllProcs spec)

mkFairRegVars :: I.Spec -> [I.Expr]
mkFairRegVars spec = mkFairSchedVar : (map (mkFairProcVar . fst) $ I.specAllProcs spec)

-- PID of the process making a transition

mkPIDLVarName :: String
mkPIDLVarName = "$lpid"

mkPIDLVar :: I.Expr
mkPIDLVar = I.EVar mkPIDLVarName

mkPIDEnumeratorName :: PrID -> String
mkPIDEnumeratorName pid = "$" ++ show pid

parsePIDEnumerator :: String -> PrID
parsePIDEnumerator n = parsePID $ tail n

mkPIDEnum :: PrID -> I.Expr
mkPIDEnum = I.EConst . I.EnumVal . mkPIDEnumeratorName

mkPIDEnumName :: String
mkPIDEnumName = "$pidenum" 

--mkEPIDNone :: String
--mkEPIDNone = "$epidnone"

mkPIDLVarDecl :: [PrID] -> (I.Var, I.Enumeration)
mkPIDLVarDecl pids = (I.Var False I.VarTmp mkPIDLVarName (I.Enum Nothing mkPIDEnumName), enum)
    where enum = I.Enumeration mkPIDEnumName $ map mkPIDEnumeratorName pids

--mkContVarName :: String
--mkContVarName = "$cont"
--
--mkContVar :: I.Expr
--mkContVar = I.EVar mkContVarName
--
--mkContVarDecl :: (?spec::Spec) => I.Var
--mkContVarDecl = I.Var False I.VarState mkContVarName I.Bool

mkContLVarName :: String
mkContLVarName = "$lcont"

mkContLVar :: I.Expr
mkContLVar = I.EVar mkContLVarName

mkContLVarDecl :: (?spec::Spec) => I.Var
mkContLVarDecl = I.Var False I.VarTmp mkContLVarName (I.Bool Nothing)

mkMagicVarName :: String
mkMagicVarName = "$magic"

mkMagicVar :: I.Expr
mkMagicVar = I.EVar mkMagicVarName

mkMagicVarDecl :: I.Var
mkMagicVarDecl = I.Var False I.VarState mkMagicVarName (I.Bool Nothing)

mkMagicDoneCond :: I.Expr
mkMagicDoneCond = mkMagicVar I.=== I.false

mkErrVarName :: String
mkErrVarName = I.cfaErrVarName

mkErrVar :: I.Expr
mkErrVar = I.EVar mkErrVarName

mkErrVarDecl :: I.Var
mkErrVarDecl = I.Var False I.VarState mkErrVarName (I.Bool Nothing)

mkTagVarName :: String
mkTagVarName = "$tag"

mkTagVar :: I.Expr
mkTagVar = I.EVar mkTagVarName

mkTagExit      = "$tagexit" -- exit magic block
mkTagDoNothing = "$tagnop"  -- idle loop transition
-- mkTagNone = "$tagnone"

mkTagVarDecl :: (?spec::Spec) => (I.Var, I.Enumeration)
mkTagVarDecl = (I.Var False I.VarTmp mkTagVarName (I.Enum Nothing "$tags"), I.Enumeration "$tags" mkTagList)

mkTagList :: (?spec::Spec) => [String]
mkTagList = mkTagExit :
            mkTagDoNothing :
            (map sname
             $ filter ((== Task Controllable) . methCat)
             $ tmMethod tmMain)

mkArgTmpVarName :: Method -> Arg -> String
mkArgTmpVarName m a = "$$" ++ sname m ++ "." ++ sname a

mkChoiceTypeName :: Int -> String
mkChoiceTypeName n = "$choice" ++ show n

mkChoiceType :: Int -> I.Type
mkChoiceType n = I.Enum Nothing $ mkChoiceTypeName n

mkChoiceValName :: String -> Int -> String
mkChoiceValName tname i = tname ++ "_" ++ show i

mkChoice :: I.Var -> Int -> I.Expr
mkChoice v i = I.EConst $ I.EnumVal $ mkChoiceValName tname i
    where I.Enum _ tname = I.varType v 

mkChoiceEnumDecl :: Int -> I.Enumeration
mkChoiceEnumDecl i = I.Enumeration {..}
    where enumName  = mkChoiceTypeName i
          enumEnums = map (mkChoiceValName enumName) [0..i-1]

type NameMap = M.Map Ident I.Expr

methodLMap :: Maybe PrID -> Method -> NameMap 
methodLMap mpid meth = 
    M.fromList $ map (\v -> (name v, mkVar (NSID mpid (Just meth)) v)) (methVar meth) ++
                 map (\a -> (name a, mkVar (NSID mpid (Just meth)) a)) (methArg meth)

procLMap :: Process -> NameMap
procLMap p = M.fromList $ map (\v -> (name v, mkVar (NSID (Just $ PrID (sname p) []) Nothing) v)) (procVar p)

xducerLMap :: Transducer -> NameMap
xducerLMap x@Transducer{..} = M.fromList $ inputs ++ outputs ++ locals
    where inputs = map (\i -> (name i, I.EVar $ sname i)) txInput
          outputs = map (\o -> (name o, I.EVar $ sname o)) txOutput
          locals = case txBody of
                        Left _   -> []
                        Right st -> map (\v -> (name v, I.EVar $ sname v)) $ stmtVar st

scopeLMap :: Maybe PrID -> Scope -> NameMap
scopeLMap mpid sc = 
    case sc of
         ScopeMethod   _ meth -> methodLMap mpid meth
         ScopeProcess  _ proc -> procLMap proc
         ScopeTransducer tx   -> xducerLMap tx
         ScopeTemplate _      -> M.empty
 
globalNMap :: (?spec::Spec) => NameMap
globalNMap = M.union (M.fromList $ gvars ++ wires) globalConstNMap
    where -- global variables
          gvars  = map (\v -> (name v, mkVar (NSID Nothing Nothing) v)) $ tmVar tmMain
          -- wires
          wires  = map (\w -> (name w, mkVar (NSID Nothing Nothing) w)) $ tmWire tmMain

globalConstNMap :: (?spec::Spec) => NameMap
globalConstNMap = M.fromList $ enums ++ consts
    where enums  = concatMap (\d -> case tspec d of
                                            EnumSpec _ es -> map (\e -> (name e, I.EConst $ I.EnumVal $ sname e)) es
                                            _             -> []) 
                             $ specType ?spec
          consts = let ?scope = ScopeTop
                   in mapMaybe (\c -> case eval $ constVal c of
                                           TVal _ (StructVal _) -> Nothing
                                           v                    -> Just (name c, I.EConst $ valToIVal v))
                      $ specConst ?spec

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------

valToIVal :: (?spec::Spec) => TVal -> I.Val
valToIVal (TVal _ (BoolVal True))  = I.BoolVal True
valToIVal (TVal _ (BoolVal False)) = I.BoolVal False
valToIVal (TVal t (IntVal i))      = case tspec $ typ' t of 
                                          SIntSpec _ w -> I.SIntVal w i
                                          UIntSpec _ w -> I.UIntVal w i
valToIVal (TVal _ (EnumVal n))     = I.EnumVal $ sname n

mkType :: (?spec::Spec) => Type -> I.Type
mkType t = 
    case typ' t of
         Type _ (BoolSpec     _)      -> I.Bool alias
         Type _ (SIntSpec     _ w)    -> I.SInt alias w
         Type _ (UIntSpec     _ w)    -> I.UInt alias w
         Type s (StructSpec   _ fs)   -> I.Struct alias $ map (\(Field _ t' n) -> I.Field (sname n) (mkType (Type s t'))) fs 
         Type _ (EnumSpec     _ es)   -> I.Enum alias $ getEnumName $ name $ head es
         Type s (PtrSpec      _ t')   -> I.Ptr alias $ mkType $ Type s t'
         Type s (ArraySpec    _ t' l) -> let ?scope = s in I.Array alias (mkType $ Type s t') (fromInteger $ evalInt l)
         Type s (VarArraySpec _ t')   -> let ?scope = s in I.VarArray alias (mkType $ Type s t')
         Type s (SeqSpec _ t')        -> let ?scope = s in I.Seq alias (mkType $ Type s t')
         Type _ t'                    -> error $ "mkType: " ++ show t'
    where alias = case tspec t of
                       UserTypeSpec _ a -> Just $ render $ pp a
                       _                -> Nothing


getEnumName :: (?spec::Spec) => Ident -> String
getEnumName n = 
    sname $ fromJustMsg ("getEnumName: enumerator " ++ sname n ++ " not found") $
    find (\d -> case tspec d of
                     EnumSpec _ es -> isJust $ find ((==n) . name) es
                     _             -> False) 
         $ specType ?spec

-----------------------------------------------------------
-- State maintained during CFA construction
-----------------------------------------------------------

data CFACtx = CFACtx { ctxEPID    :: Maybe EPID                              -- ID of the CFA being constructed or Nothing if the CFA is not part of the final spec
                     , ctxStack   :: [(Scope, I.Loc, Maybe I.Expr, NameMap)] -- stack of syntactic scopes: (scope, return location, LHS, local namemap)
                     , ctxCFA     :: I.CFA                                   -- CFA constructed so far
                     , ctxBrkLocs :: [I.Loc]                                 -- stack break location
                     , ctxGNMap   :: NameMap                                 -- global variables visible in current scope
                     , ctxLastVar :: Int                                     -- counter used to generate unique variable names
                     , ctxVar     :: [I.Var]                                 -- temporary vars
                     , ctxLabels  :: [String]                                -- statement label stack
                     }

ctxScope :: CFACtx -> Scope
ctxScope = sel1 . head . ctxStack

ctxRetLoc :: CFACtx -> I.Loc
ctxRetLoc = sel2 . head . ctxStack

ctxLHS :: CFACtx -> Maybe I.Expr
ctxLHS = sel3 . head . ctxStack

ctxLNMap :: CFACtx -> NameMap
ctxLNMap = sel4 . head . ctxStack

ctxPushScope :: Scope -> I.Loc -> Maybe I.Expr -> NameMap -> State CFACtx ()
ctxPushScope sc retloc lhs nmap = modify (\ctx -> ctx {ctxStack = (sc, retloc, lhs, nmap) : (ctxStack ctx)})

ctxPopScope :: State CFACtx ()
ctxPopScope = modify (\ctx -> ctx {ctxStack = tail $ ctxStack ctx})

ctxBrkLoc :: CFACtx -> I.Loc
ctxBrkLoc = head . ctxBrkLocs

ctxPushBrkLoc :: I.Loc -> State CFACtx ()
ctxPushBrkLoc loc = modify (\ctx -> ctx {ctxBrkLocs = loc : (ctxBrkLocs ctx)})

ctxPopBrkLoc :: State CFACtx ()
ctxPopBrkLoc = modify (\ctx -> ctx {ctxBrkLocs = tail $ ctxBrkLocs ctx})

ctxPushLabel :: String -> State CFACtx ()
ctxPushLabel lab = modify (\ctx -> ctx {ctxLabels = lab : ctxLabels ctx})

ctxPopLabel :: State CFACtx ()
ctxPopLabel = modify (\ctx -> ctx {ctxLabels = tail $ ctxLabels ctx})

ctxInsLoc :: State CFACtx I.Loc
ctxInsLoc = ctxInsLocLab (I.LInst I.ActNone)

ctxInsLocLab :: I.LocLabel -> State CFACtx I.Loc
ctxInsLocLab lab = do
    ctx <- get
    let (cfa', loc) = I.cfaInsLoc lab $ ctxCFA ctx
    put $ ctx {ctxCFA = cfa'}
    return loc

ctxLocSetAct :: I.Loc -> I.LocAction -> State CFACtx ()
ctxLocSetAct loc act = modify (\ctx -> ctx {ctxCFA = I.cfaLocSetAct loc act $ ctxCFA ctx})

ctxLocSetStack :: I.Loc -> I.Stack -> State CFACtx ()
ctxLocSetStack loc stack = modify (\ctx -> ctx {ctxCFA = I.cfaLocSetStack loc stack $ ctxCFA ctx})


ctxInsTrans :: I.Loc -> I.Loc -> I.TranLabel -> State CFACtx ()
ctxInsTrans from to t = modify (\ctx -> ctx {ctxCFA = I.cfaInsTrans from to t $ ctxCFA ctx})

ctxInsTransMany :: I.Loc -> I.Loc -> [I.TranLabel] -> State CFACtx ()
ctxInsTransMany from to ts = modify $ (\ctx -> ctx {ctxCFA = I.cfaInsTransMany from to ts $ ctxCFA ctx})

ctxInsTrans' :: I.Loc -> I.TranLabel -> State CFACtx I.Loc
ctxInsTrans' from t = do
    to <- ctxInsLoc
    ctxInsTrans from to t
    return to

ctxInsTransMany' :: I.Loc -> [I.TranLabel] -> State CFACtx I.Loc
ctxInsTransMany' from ts = do
    to <- ctxInsLoc
    ctxInsTransMany from to ts
    return to

ctxInsTmpVar :: Maybe Ident -> I.Type -> State CFACtx I.Var
ctxInsTmpVar mn t = do
    lst   <- gets ctxLastVar
    mepid <- gets ctxEPID
    sc    <- gets ctxScope
    let nsid = maybe (NSID Nothing Nothing) (\epid -> epid2nsid epid sc) mepid
        vname = mkVarNameS nsid $ maybe ("$tmp" ++ show (lst + 1)) sname mn
        v = I.Var False I.VarTmp vname t
    modify $ (\ctx -> ctx { ctxLastVar = lst + 1
                          , ctxVar     = v:(ctxVar ctx)})
    return v

ctxFrames :: I.Loc -> State CFACtx I.Stack
ctxFrames loc = do
    cfastack <- gets ctxStack
    -- CFACtx stack stores return locations in stack frames,  but the Stack 
    -- type stores current locations in frames.  Shift ret locations by one 
    -- and append current location in the end. 
    let scopes = map sel1 cfastack
        locs   = loc: (init $ map sel2 cfastack)
    return $ map (uncurry I.Frame) $ zip scopes locs


ctxPause :: I.Loc -> I.Expr -> I.LocAction -> State CFACtx I.Loc
ctxPause loc cond act = do
    labs <- gets ctxLabels
    after <- ctxInsLocLab (I.LPause act [] labs cond)
    stack <- ctxFrames after
    ctxLocSetStack after stack
    ctxInsTrans loc after $ I.TranNop
--    ctxSuffix loc after after
    ctxInsTrans' after (I.TranStat $ I.SAssume cond)

ctxIn :: I.Loc -> I.Expr -> I.Expr -> I.LocAction -> State CFACtx I.Loc
ctxIn loc elhs erhs act = do
    after <- ctxInsLocLab (I.LIn act elhs erhs)
    ctxInsTrans loc after $ I.TranNop
    return after

ctxFinal :: I.Loc -> State CFACtx I.Loc
ctxFinal loc = do 
    labs <- gets ctxLabels
    after <- ctxInsLocLab (I.LFinal I.ActNone [] labs)
    stack <- ctxFrames after
    ctxLocSetStack after stack
    ctxInsTrans loc after $ I.TranNop
--    ctxSuffix loc after after
    return after

ctxUContInsertSuffixes :: State CFACtx ()
ctxUContInsertSuffixes = do
    -- Just (EPIDProc pid) <- gets ctxEPID
    epid <- gets ctxEPID
    let (EPIDProc pid) = case epid of
            Nothing -> error $ "expected Just, was Nothing"
            Just epid2 -> epid2

    cfa0   <- gets ctxCFA
    modify $ \ctx -> ctx {ctxCFA = foldl' (insertSuffix pid) cfa0 (I.cfaDelayLocs cfa0)}
    cfa1   <- gets ctxCFA
    modify $ \ctx -> ctx {ctxCFA = foldl' (insertPrefix pid) cfa1 (I.cfaDelayLocs cfa1)}

insertPrefix :: PrID -> I.CFA -> I.Loc -> I.CFA
insertPrefix pid cfa loc | (null $ G.lsuc cfa loc) = cfa
                         | otherwise               = I.cfaInsTrans loc loc' (I.TranStat $ I.SAssume $ lepid `I.land` ucont) cfa1
    where (Just (pre, _, lab, suc), cfa0) = G.match loc cfa 
          loc' = (snd $ G.nodeRange cfa) + 1
          cfa1 = (pre, loc, lab, []) G.& (([], loc', I.LInst I.ActNone, suc) G.& cfa0)
          lepid = mkPIDLVar I.=== (mkPIDEnum pid)
          ucont = mkContLVar I.=== I.false

insertSuffix :: PrID -> I.CFA -> I.Loc -> I.CFA
insertSuffix pid cfa loc | (null $ G.pre cfa loc) = cfa
                         | otherwise              = cfa1
    where
    (loc', cfa0)  = I.cfaSplitLoc loc cfa
    -- pc
    cfa1 = I.cfaInsTrans loc' loc (mkPCAsn cfa pid (mkPC pid loc)) cfa0
    -- cont
    --cfa2          = I.cfaInsTrans  aftpc loc (I.TranStat $ mkContVar I.=: mkContLVar) cfa1

ctxErrTrans :: I.Loc -> I.Loc -> State CFACtx ()
ctxErrTrans from to = do
    modify $ \ctx -> ctx {ctxCFA = I.cfaErrTrans from to $ ctxCFA ctx}

-- Add error transitions for all potential null-pointer dereferences
ctxAddNullPtrTrans :: State CFACtx ()
ctxAddNullPtrTrans = do 
    ctx  <- get
    _ <- mapM addNullPtrTrans1 (G.labEdges $ ctxCFA ctx)
    return () 

addNullPtrTrans1 :: (I.Loc,I.Loc,I.TranLabel) -> State CFACtx ()
addNullPtrTrans1 (from , to, l@(I.TranStat (I.SAssign e1 e2))) = do
    let cond = -- We don't have access to ?spec here, hence cannot determine type of
               -- NullVal.  Keep it undefined until a separate pass.
               I.disj 
               $ map (\e -> e I.=== (I.EConst $ I.NullVal $ error "NullVal type undefined")) 
               $ I.exprPtrSubexpr e1 ++ I.exprPtrSubexpr e2
    case cond of
         I.EConst (I.BoolVal False) -> return ()
         _ -> do modify $ \ctx -> ctx {ctxCFA = G.delLEdge (from, to, l) $ ctxCFA ctx}
                 from' <- ctxInsTrans' from (I.TranStat $ I.SAssume $ I.neg cond)
                 fromerr <- ctxInsTrans' from (I.TranStat $ I.SAssume cond)
                 ctxInsTrans from' to l
                 ctxErrTrans fromerr from'
   
addNullPtrTrans1 (_    , _, _)                             = return ()



ctxPruneUnreachable :: State CFACtx ()
ctxPruneUnreachable = modify (\ctx -> ctx {ctxCFA = I.cfaPruneUnreachable (ctxCFA ctx) [I.cfaInitLoc]})

