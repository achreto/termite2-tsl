{-# LANGUAGE RecordWildCards, ImplicitParams, TupleSections, ScopedTypeVariables #-}

module TSL2Boogie.Spec2Boogie(spec2Boogie) where

import Prelude hiding ((<>))

import qualified Data.Map             as M
import Data.Maybe
import Data.List
import qualified Data.Graph.Inductive as IG
import qualified Data.Graph.Dom       as G
import Data.Tuple.Select
import Text.PrettyPrint

import PP
import Ops
import Util
import Internal.CFA
import Internal.ISpec
import Internal.ITransducer
import Internal.IVar
import Internal.IType
import Internal.IExpr


type Path = [String]

ppPath p = hcat $ punctuate (char '.') (map text p)

-- alphabet symbol: input port name:field names. [] = init symbol
type Symbol = [String]

showSymbol s = hcat $ punctuate (char '.') (map text s)

sym2Expr :: Symbol -> Expr
sym2Expr [port] = EVar port
sym2Expr sym    = EField (sym2Expr $ init sym) (last sym)

symbolType :: (?spec::Spec) => Symbol -> Type
symbolType sym = let Seq _ t = exprType $ sym2Expr sym in t 


spec2Boogie :: Spec -> Either String Doc
spec2Boogie spec = if any ((== "main") . txName) $ specXducers spec
                      then Right $ mkXducers spec
                      else Left "no main transducer found"

mkXducers :: Spec -> Doc
mkXducers spec = vcat $ punctuate (pp "") $ [ vcat $ map mkOpDecl ops
                                            , collectTypes spec
                                            , xducers
                                            , mkMain spec]
    where -- vs      = collectVars [] $ getXducer "main"
          main = getXducer spec "main"
          xducers = mkXducer spec [] main (replicate (length $ txInput main) True) (replicate (length $ txOutput main) [])
          ops = collectOps spec main

getXducer :: Spec -> String -> Transducer
getXducer spec n = fromJustMsg ("fromJust Nothing getXducer" {-intercalate "," $ n : (map txName $ specXducers ?spec)-}) $ find ((== n) . txName) $ specXducers spec

collectOps :: Spec -> Transducer -> [(Either UOp BOp, Int)]
collectOps spec x = 
    case txBody x of
         Left (_,is) -> nub $ concatMap (collectOps spec . getXducer spec . tiTxName) is
         Right (cfa,_)  -> let ?spec = forXducer spec x in collectOpsCFA cfa

collectOpsCFA :: (?spec::Spec) => CFA -> [(Either UOp BOp, Int)]
collectOpsCFA cfa = nub $ concatMap (\e -> case sel3 e of
                                                TranStat s -> collectOpsStat s
                                                _          -> [])
                        $ IG.labEdges cfa

collectOpsStat :: (?spec::Spec) => Statement -> [(Either UOp BOp, Int)]
collectOpsStat (SAssume e)   = collectOpsExpr e
collectOpsStat (SAssert e)   = collectOpsExpr e
collectOpsStat (SAssign l r) = nub $ collectOpsExpr l ++ collectOpsExpr r
collectOpsStat (SOut l r)    = nub $ collectOpsExpr l ++ collectOpsExpr r

collectOpsExpr :: (?spec::Spec) => Expr -> [(Either UOp BOp, Int)]
collectOpsExpr (EVar _)          = []
collectOpsExpr (EConst _)        = []
collectOpsExpr (EField e _)      = collectOpsExpr e
collectOpsExpr (EIndex a i)      = nub $ collectOpsExpr a ++ collectOpsExpr i
collectOpsExpr (ERange e (f,t))  = nub $ collectOpsExpr e ++ collectOpsExpr f ++ collectOpsExpr t
collectOpsExpr (ELength e)       = collectOpsExpr e
collectOpsExpr (EUnOp op e)      = nub $ (Left op, exprWidth e) : collectOpsExpr e
collectOpsExpr (EBinOp op e1 e2) = nub $ (Right op, exprWidth e1) : collectOpsExpr e1 ++ collectOpsExpr e2
collectOpsExpr (ESlice e _)      = collectOpsExpr e

collectTypes :: Spec -> Doc
collectTypes spec = vcat $ stenums ++ (map (let ?spec = spec in uncurry mkType) $ foldl' add [] types)
    where add :: [(Type, [String])] -> Type -> [(Type, [String])]
          add []      t = [(t,[])]
          add ((t0,as):ts) t = case (t0,t) of
                                    (Struct _ fs1, Struct (Just n2) fs2) -> if' (fs1 == fs2) ((t0,n2:as):ts) ((t0,as):(add ts t))
                                    _                                    -> (t0,as):(add ts t)
          types = nub $ concatMap collectTypes' $ specXducers spec
          -- state enum
          stenums = mapMaybe (\x -> case txBody x of
                                         Left _        -> Nothing
                                         Right (cfa,_) -> Just $ mkEnumType n $ map (render . stateName x) locs
                                                          where locs = delete cfaInitLoc (cfaDelayLocs cfa)
                                                                n = render $ stateTypeName x)
                    $ specXducers spec

collectTypes' :: Transducer -> [Type]
collectTypes' Transducer{..} = 
    case txBody of
         Left _        -> []
         Right (_, vs) -> nub $ (concatMap (collectTypesT . varType) vs) ++ 
                                (concatMap (collectTypesT . fst) txOutput) ++
                                (concatMap (collectTypesT . fst) txInput)

-- Bools and bitvectors are builtins in Boogie - ignore them.
-- Strip sequence types.
collectTypesT :: Type -> [Type]
collectTypesT t@(Enum _ _)     = [t]
collectTypesT t@(Struct _ fs)  = nub $ t:(concatMap (\(Field _ t) -> collectTypesT t) fs)
collectTypesT   (Ptr _ _)      = error "Pointer type in transducer"
collectTypesT   (Seq _ t)      = collectTypesT t         
collectTypesT t@(Array _ t' _) = nub $ t:(collectTypesT t')
collectTypesT   (VarArray _ _) = error "VarArray type in transducer"
collectTypesT   _              = []

typeName :: Type -> Doc
typeName (Bool _)            = text "bool"
typeName (SInt _ _)          = error "Not implemented: signed bitvectors in Spec2Boogie.hs"
typeName (UInt _ w)          = text $ "bv" ++ show w
typeName (Enum _ e)          = text e
typeName (Struct Nothing _)  = error "Not implemented: anonymous struct in Spec2Boogie.hs"
typeName (Struct (Just n) _) = text n
typeName (Array _ _ _)       = error "Not implemented: arrays in Spec2Boogie.hs"
typeName t                   = error $ "typeName " ++ show t


mkEnumType :: String -> [String] -> Doc
mkEnumType n es = (text "type" <+> {-text "finite" <+>-} text n <> semi)
                  $$
                  (vcat $ map (\e -> text "const" <+> text "unique" <+> text e <> colon <+> text n <> semi) es)
                  $$
                  (text "axiom" <+> parens (text "forall" <+> text "_x" <> colon <+> text n <> text "::" <+> disj) <> semi)
    where disj = hcat $ punctuate (text "||") $ map (\e -> text "_x" <+> text "==" <+> text e) es

mkType :: (?spec::Spec) => Type -> [String] -> Doc
mkType (Enum _ n)  _    = mkEnumType n es
    where Enumeration _ es = getEnumeration n 
mkType (Struct mn fs) as = (text "type" <+> text "{:datatype}" <+> pp n <> semi)
                           $$
                           (text "function" <+> text "{:constructor}" <+> pp n <> parens args) <+> colon <+> pp n <> semi
                           $$
                           (vcat $ map (\a -> text "type" <+> text a <+> char '=' <+> pp n <> semi) as)
    where Just n = mn
          args = hsep
                 $ punctuate comma
                 $ map (\(Field nm t) -> text nm <> colon <> typeName t)
                 $ filter (not . isSeq) fs

-- Thread input port of a transducer to a list of simple transducer instances that implement this port
-- also works if port is the name of a local instance
findPortConns :: Spec -> Transducer -> Path -> [[(Path, String)]] -> TxPortRef -> [(Path, String)]
findPortConns spec x p fanout port = 
    case txBody x of
         Left (refs, is) -> (concatMap (\TxInstance{..} -> 
                             let x' = getXducer spec tiTxName 
                                 fanout' = map (\(_, o) -> findPortConns spec x p fanout (TxLocalRef tiTxName o)) $ txOutput x' in
                             concatMap (\(_,(_,prt)) -> findPortConns spec x' (p++[tiInstName]) fanout' (TxInputRef prt)) 
                                       $ filter ((== Just port) . fst) 
                                       $ zip tiInputs (txInput x')) is) ++
                            (concatMap snd $ filter ((== port) . fst) $ zip refs fanout)
         Right _ -> let TxInputRef n = port in [(p,n)]

mkXducer :: Spec -> Path -> Transducer -> [Bool] -> [[(Path, String)]] -> Doc
mkXducer spec p x fanin fanout =
    case txBody x of
         -- composite transducer
         Left (ref,is) -> -- print instances; route each instance output to other instance inputs or to the top-level output
                    vcat $ punctuate (text "") 
                    $ (mapIdx (\i id -> mkXducer spec (p++[tiInstName i]) (getXducer spec $ tiTxName i) (map isJust (tiInputs i)) (connect i)) is)
                    where -- compute list of ports that an instance is connected to
                          connect :: TxInstance -> [[(Path, String)]]
                          connect i = map (\(_,o) -> findPortConns spec x p fanout (TxLocalRef (tiInstName i) o)) $ txOutput x'
                                     where x' = getXducer spec (tiTxName i)
         -- simple transducer
         Right (_,vs) -> let ?spec = forXducer spec x in mkXducer' p x fanin fanout

mkMain :: Spec -> Doc
mkMain spec = 
    let main = getXducer spec "main" in
    let ?spec = forXducer spec main in
    let -- input port of the main xducer
        (ptype, pname) = head $ txInput main
        ports = findPortConns spec main [] (map (\_ -> []) $ txOutput main) (TxInputRef pname)
        decls = vcat $ map mkSymVar $ symChildrenRec ptype [pname]
        inits = mkInit [] main
        mkInit :: Path -> Transducer -> Doc
        mkInit p x = case txBody x of
                          Left (_, is) -> vcat $ map (\i -> mkInit (p++[tiInstName i]) (getXducer spec $ tiTxName i)) is
                          Right _      -> call (initializerName p) []
    in procedure (pp "main") [] $ decls $+$ inits $+$ mkGen main ports [pname]


mkGen :: (?spec::Spec) => Transducer -> [(Path,String)] -> Symbol -> Doc
mkGen x ports sym = while (pp "*") body
    where 
    body = (if isSeq $ symbolType sym
               then empty
               else (havoc $ showSymbol sym)
                    $+$
                    (vcat $ map (\(path,port) -> call (handlerName path (port:tail sym)) [showSymbol sym]) ports))
           $+$
           (vcat $ map (mkGen x ports) $ symChildren (symbolType sym) sym)

symChildren :: Type -> Symbol -> [Symbol]
symChildren t sym = 
    case t of
         Struct _ fs -> concatMap (\(Field fn ft) -> if' (isSeq ft) [sym++[fn]] []) fs
         _           -> []

symChildrenRec :: Type -> Symbol -> [Symbol]
symChildrenRec (Seq _ (Struct _ fs)) ns = (concatMap (\(Field fn ft) -> symChildrenRec ft (ns++[fn])) fs) ++ [ns]
symChildrenRec (Seq _ t)             ns = [ns]
symChildrenRec _                     _  = []

forXducer :: Spec -> Transducer -> Spec
forXducer spec x = let invars = map (\(t,nm) -> Var False VarState nm t) $ txInput x
                       outvars = map (\(t,nm) -> Var False VarState nm t) $ txOutput x
                   in case txBody x of
                           Left _       -> spec {specVar = invars ++ outvars}
                           Right (_,vs) -> spec {specVar = vs ++ invars ++ outvars}

procedure :: Doc -> [(Doc, Doc)] -> Doc -> Doc
procedure nm args body = (text "procedure" <+> nm <+> 
                          (parens $ hcat $ punctuate (pp ", ") $ map (\(n,t) -> n <> colon <> t) args)) 
                         $+$ lbrace $+$ (nest' body) $+$ rbrace

call :: Doc -> [Doc] -> Doc
call f args = text "call" <+> f <+> (parens $ hsep $ punctuate comma args) <> semi

assign :: Doc -> Doc -> Doc
assign l r = l <+> text ":=" <+> r <> semi

while :: Doc -> Doc -> Doc
while cond body = (pp "while" <+> (parens cond) <+> lbrace)
                  $+$
                  (nest' body)
                  $+$
                  rbrace

havoc :: Doc -> Doc
havoc x = text "havoc" <+> x <> semi

var :: Doc -> Doc -> Doc
var n t = text "var" <+> n <+> char ':' <+> t <> semi

mkSymVar :: (?spec::Spec) => Symbol -> Doc
mkSymVar s = var (showSymbol s) (typeName $ symbolType s)

-- Print simple transducer:
mkXducer' :: (?spec::Spec) => Path -> Transducer -> [Bool] -> [[(Path, String)]] -> Doc
mkXducer' p x@Transducer{..} fanin fanout = vcat $ punctuate (text "") (vars:initproc:handlers)
    where 
    Right (cfa, vs) = txBody

    isConnected :: Expr -> Bool
    isConnected e = fanin !! (fromJust $ findIndex ((==(head $ expr2Sym e)) . snd) txInput)

    insymbols::[Symbol] = concatMap (\(t,n) -> symChildrenRec t [n]) txInput
    outsymbols::[Symbol] = concatMap (\(t,n) -> symChildrenRec t [n]) txOutput

    -- states along with the symbol acceped in each state
    states :: [(Loc,Maybe Symbol)]
    states = mapMaybe  (\loc -> if' (loc == cfaInitLoc) (Just (loc, Just []))
                                    (case cfaLocLabel loc cfa of
                                          LFinal _ _ _ -> Just (loc, Nothing)
                                          LIn _ _ r    -> if isConnected r
                                                             then Just (loc, Just $ expr2Sym r)
                                                             else Nothing))
             $ cfaDelayLocs cfa

    expr2Sym :: Expr -> Symbol
    expr2Sym (EVar n)     = [n]
    expr2Sym (EField e f) = (expr2Sym e)++[f]

    ([(initst,_)], states') = partition (null . fromJustMsg "mkXducer" . snd) $ filter (isJust . snd) states
    -- transition CFAs
    (initSink, initCFA) = cfaAddUniqueSink $ cfaLocTransCFA cfa (map fst states) initst
    cfas::M.Map Symbol [(Loc,Loc,CFA)] 
    cfas = M.fromList
           $ map (\ss -> (fromJustMsg "mkXducer" $ snd $ head ss, map ((\l -> let (sink, cfa') = cfaAddUniqueSink $ cfaLocTransCFA cfa (map fst states) l
                                                                in (l, sink, cfa')) . fst) ss))
           $ sortAndGroup snd states'

    -- the post-dominator algorithm requires a unique sink
    cfaAddUniqueSink :: CFA -> (Loc, CFA)
    cfaAddUniqueSink cfa = (sink, foldl' (\c loc -> cfaInsTrans loc sink TranNop c) cfa' $ cfaSink cfa)
        where (cfa',sink) = cfaInsLoc (LInst ActNone) cfa

    -- state var
    stvar = var (stateVarName p) (stateTypeName x)

    -- local vars
    lvars = map (\v -> var (xvarName p $ varName v) (typeName $ varType v)) vs

    vars = vcat $ stvar : text "" : lvars

    -- init method
    initproc = procedure (initializerName p) [] $ mkCFA (initst, initSink, initCFA) 
    
    -- input handlers
    handlers = map mkHandler insymbols

    mkHandler :: Symbol -> Doc
    mkHandler sym = procedure (handlerName p sym) [(showSymbol sym, typeName $ symbolType sym)] body
        where
        -- for each state where sym is handled, generate code from CFA
        handlers = maybe [] 
                         (map (\(loc, sink, cfa') -> let LIn _ l _ = cfaLocLabel loc cfa in
                                                     (stateVarName p <+> pp "==" <+> stateName x loc, 
                                                     assign (mkExpr l) (showSymbol sym) $+$ mkCFA (loc, sink, cfa'))))
                         (M.lookup sym cfas)

        -- generate empty handlers (loop transitions) for all states where sym's parent is handled
--        parents = init $ tail $ inits sym
--        parentlocs = concatMap (\sym' -> maybe [] (map sel1) $ M.lookup sym' cfas) parents
--        loops = if null parents 
--                   then []
--                   else [(hsep $ punctuate (text "&&") $ map (\loc -> stateVarName p <+> text "==" <+> stateName x loc) parentlocs, empty)]

        body = mkSwitch (handlers ++ {-loops ++-} [(undefined, text "assert(false);")])

    mkSwitch :: [(Doc, Doc)] -> Doc
    mkSwitch [(_,defaction)]       = defaction -- throw error otherwise
    mkSwitch ((cond, action):rest) = ((text "if" <+> (parens cond) <+> lbrace) $+$ (nest' action))
                                     $+$ 
                                     (if' (null $ tail rest)
                                          ((rbrace <+> text "else" <+> lbrace) $+$ (nest' $ mkSwitch rest) $+$ rbrace)
                                          (zeroWidthText "} else " <> mkSwitch rest))

    mkCFA :: (Loc, Loc, CFA) -> Doc
    mkCFA (from, sink, cfa) = mkCFA' (from, sink, cfa) sink
    
    mkCFA' :: (Loc, Loc, CFA) -> Loc -> Doc
    mkCFA' (from, sink, cfa) to | from == to        = empty                                             -- stop at the "to" node
                                | loc0 == sink      = assign (stateVarName p) (stateName x from)        -- final location
                                | null (tail trans) = mkTransition lab0 loc0 $+$ mkCFA' (loc0, sink, cfa) to -- single successor
                                | otherwise         = (mkSwitch 
                                                        $ map (\(tlab,loc) -> (text "*", mkTransition tlab loc $+$ mkCFA' (loc, sink,cfa) pdom)) trans)
                                                       $+$
                                                       mkCFA' (pdom, sink, cfa) to 
        where trans@((lab0,loc0):_) = cfaSuc from cfa
              -- postdominator of from
              --doms = G.idom (sink, G.fromEdges $ map swap $ IG.edges cfa)
              cfa'::CFA = IG.mkGraph (IG.labNodes cfa) $ map (\(from, to, l) -> (to,from,l)) $ IG.labEdges cfa
              doms = IG.iDom cfa' sink
              pdom = fromJustMsg "mkCFA" $ lookup from doms 

    mkTransition :: TranLabel -> Loc -> Doc
    mkTransition lab loc = mkTransition' lab $+$ rand
        where rand = case cfaLocLabel loc cfa of
                          LIn  _ l r -> if isConnected r
                                           then empty
                                           else havoc $ mkExpr l
                          _          -> empty

    mkTransition' :: TranLabel -> Doc
    mkTransition' (TranStat (SAssume e))   = text "assume" <> (parens $ mkExpr e) <> semi
    mkTransition' (TranStat (SAssert e))   = text "assert" <> (parens $ mkExpr e) <> semi
    mkTransition' (TranStat (SAssign l r)) = mkAssign l r
    mkTransition' (TranStat (SOut l r))    = mkOut l r
    mkTransition' TranNop                  = empty

    mkAssign :: Expr -> Expr -> Doc
    mkAssign l r = mkAssign' l [] r
    
    mkAssign' :: Expr -> [String] -> Expr -> Doc
    mkAssign' (EField e f) fs r = mkAssign' e (fs ++ [f]) r
    mkAssign' l fs r            = assign (mkExpr l) $ mkAssignRHS l fs r

    mkAssignRHS :: Expr -> [String] -> Expr -> Doc
    mkAssignRHS _ [] r = mkExpr r
    mkAssignRHS l (f:fs) r = pp n <> (parens $ hsep $ punctuate comma 
                                      $ map (\(Field fn ft) -> if' (fn == f) (mkAssignRHS l' fs r) (mkExpr $ EField l fn)) fts)
        where l' = EField l f
              Struct (Just n) fts = exprType l

    mkOut :: Expr -> Expr -> Doc
    mkOut l r = out
        where sym = expr2Sym r
              portidx = fromJust $ findIndex ((==head sym) . snd) txOutput
              out = vcat 
                    $ map (\(path,port) -> call (handlerName path (port:tail sym)) [mkExpr l])
                    $ fanout !! portidx

    mkExpr :: Expr -> Doc
    mkExpr (EVar v)                = xvarName p v
    mkExpr (EConst v)              = mkConst v
    mkExpr (EField e f)            = let tn = typeName $ exprType e in text f <> char '#' <> tn <> (parens $ mkExpr e)
    mkExpr (EUnOp Not e)           = parens $ char '!' <> mkExpr e
    mkExpr (EUnOp BNeg e)          = text ("BV"++(show $ exprWidth e)++"_NOT") <> (parens $ mkExpr e)
    mkExpr (EBinOp Eq e1 e2)       = parens $ mkExpr e1 <+> text "==" <+> mkExpr e2
    mkExpr (EBinOp Neq e1 e2)      = parens $ mkExpr e1 <+> text "!=" <+> mkExpr e2
    mkExpr (EBinOp Lt e1 e2)       = bvbop Lt e1 e2
    mkExpr (EBinOp Gt e1 e2)       = bvbop Gt e1 e2
    mkExpr (EBinOp Lte e1 e2)      = bvbop Lte e1 e2
    mkExpr (EBinOp Gte e1 e2)      = bvbop Gte e1 e2
    mkExpr (EBinOp And e1 e2)      = parens $ mkExpr e1 <+> text "&&" <+> mkExpr e2
    mkExpr (EBinOp Or e1 e2)       = parens $ mkExpr e1 <+> text "||" <+> mkExpr e2
    mkExpr (EBinOp Imp e1 e2)      = parens $ mkExpr e1 <+> text "==>" <+> mkExpr e2
    mkExpr (EBinOp BAnd e1 e2)     = bvbop BAnd e1 e2
    mkExpr (EBinOp BOr e1 e2)      = bvbop BOr e1 e2
    mkExpr (EBinOp BXor e1 e2)     = bvbop BXor e1 e2
    mkExpr (EBinOp BConcat e1 e2)  = parens $ mkExpr e2 <+> text "++" <+> mkExpr e1
    mkExpr (EBinOp Plus e1 e2)     = bvbop Plus e1 e2
    mkExpr (EBinOp BinMinus e1 e2) = bvbop BinMinus e1 e2
    mkExpr (EBinOp Mul e1 e2)      = bvbop Mul e1 e2
    mkExpr (ESlice e (l,h))        = mkExpr e <> (brackets $ pp h <> char ':' <> pp l)

    bvbop op e1 e2 = text ("BV"++(show $ exprWidth e1)++"_"++bvbopname op) <> (parens $ mkExpr e1 <> comma <+> mkExpr e2)

    mkConst :: Val -> Doc
    mkConst (BoolVal True)     = pp "true"
    mkConst (BoolVal False)    = pp "false"
    mkConst (UIntVal w v)      = pp v <> text "bv" <> pp w
    mkConst (EnumVal n)        = pp n

xvarName :: Path -> String -> Doc
xvarName p v = ppPath p <> char '_' <> pp v

handlerName :: Path -> Symbol -> Doc
handlerName p s = xvarName p $ "handle_" ++ (render $ showSymbol s)

stateVarName :: Path -> Doc
stateVarName p = xvarName p "_state"

stateName :: Transducer -> Loc -> Doc
stateName x l = (text $ txName x) <> pp "_" <> pp l

stateTypeName :: Transducer -> Doc
stateTypeName x = (pp $ txName x) <> pp "_state_t"

initializerName :: Path -> Doc 
initializerName p = ppPath p <> pp "_init"

mkOpDecl :: (Either UOp BOp, Int) -> Doc
mkOpDecl (Right Lt      , w) = mkBOpDecl "bvult" (bvbopname Lt)       w "bool" 
mkOpDecl (Right Gt      , w) = mkBOpDecl "bvugt" (bvbopname Gt)       w "bool" 
mkOpDecl (Right Lte     , w) = mkBOpDecl "bvule" (bvbopname Lte)      w "bool" 
mkOpDecl (Right Gte     , w) = mkBOpDecl "bvuge" (bvbopname Gte)      w "bool" 
mkOpDecl (Right BAnd    , w) = mkBOpDecl "bvand" (bvbopname BAnd)     w (bvtname w)
mkOpDecl (Right BOr     , w) = mkBOpDecl "bvor"  (bvbopname BOr)      w (bvtname w)
mkOpDecl (Right BXor    , w) = mkBOpDecl "bvxor" (bvbopname BXor)     w (bvtname w)
mkOpDecl (Right Plus    , w) = mkBOpDecl "bvadd" (bvbopname Plus)     w (bvtname w)
mkOpDecl (Right BinMinus, w) = mkBOpDecl "bvsub" (bvbopname BinMinus) w (bvtname w)
mkOpDecl (Right Mul     , w) = mkBOpDecl "bvmul" (bvbopname Mul)      w (bvtname w)
mkOpDecl (Left  BNeg    , w) = mkUOpDecl "bvnot" "BNOT"               w (bvtname w)
mkOpDecl _                   = empty

mkBOpDecl builtin opname w retname = pp $ "function {:bvbuiltin \"" ++ builtin ++ "\"} BV" ++ show w ++ "_" ++ opname ++ "(x:" ++ bvtname w ++ ", " ++ "y:" ++ bvtname w ++ ")" ++ " returns (" ++ retname ++ ");"
mkUOpDecl builtin opname w retname = pp $ "function {:bvbuiltin \"" ++ builtin ++ "\"} BV" ++ show w ++ "_" ++ opname ++ "(x:" ++ bvtname w ++ ")" ++ " returns (" ++ retname ++ ");"

bvbopname Lt       = "ULT"
bvbopname Gt       = "UGT"
bvbopname Lte      = "ULEQ"
bvbopname Gte      = "UGEQ"
bvbopname BAnd     = "AND"
bvbopname BOr      = "OR"
bvbopname BXor     = "XOR"
bvbopname Plus     = "ADD"
bvbopname BinMinus = "SUB"
bvbopname Mul      = "MULT"

bvtname w = "bv" ++ show w
