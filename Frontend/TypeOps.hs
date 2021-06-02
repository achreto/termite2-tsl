{-# LANGUAGE ImplicitParams, FlexibleContexts #-}

module Frontend.TypeOps(mapTSpec,
                        fieldType,
                        tspecMapExpr,
                        typ', 
                        typeIso,
                        typeMatch,
                        checkTypeMatch,
                        typeComparable,
                        typeWidth,
                        typeSigned,
                        isInt, isBool, isPtr, isArray, isStruct, isSequence, isSeqContainer,
                        tdeclGraph) where

import Control.Monad.Except
import Data.List
import qualified Data.Map as M
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G
import Debug.Trace

import TSLUtil
import Name
import Pos
import Frontend.Type
import Frontend.Template
import Frontend.Spec
import Frontend.NS
import Frontend.Expr
import {-# SOURCE #-} Frontend.ExprOps


fieldType :: (?spec::Spec, ?scope::Scope) => Field -> Type
fieldType = Type ?scope . tspec

-- Map function over TypeSpec
mapTSpec :: (?spec::Spec) => (Scope -> TypeSpec -> TypeSpec) -> Scope -> TypeSpec -> TypeSpec
mapTSpec f s (StructSpec p fs)    = f s $ StructSpec p (map (\fl -> Field (pos fl) (mapTSpec f s $ tspec fl) (name fl)) fs)
mapTSpec f s (PtrSpec p t)        = f s $ PtrSpec p (mapTSpec f s t)
mapTSpec f s (ArraySpec p t l)    = f s $ ArraySpec p (mapTSpec f s t) l
mapTSpec f s (VarArraySpec p t)   = f s $ VarArraySpec p (mapTSpec f s t)
mapTSpec f s (SeqSpec p t)        = f s $ SeqSpec p (mapTSpec f s t)
mapTSpec f s t = f s t

-- Map function over expressions in TypeSpec
tspecMapExpr :: (?spec::Spec) => (Scope -> Expr -> Expr) -> Scope -> TypeSpec -> TypeSpec
tspecMapExpr f s (ArraySpec p t l) = ArraySpec p t (f s l)
tspecMapExpr _ _ t                 = t

-- Expand top-level type reference
typ' :: (?spec::Spec, WithType a) => a -> Type
typ' x = case tspec $ typ x of
              UserTypeSpec _ n -> let (d,s') = getTypeDecl (scope $ typ x) n
                                  in typ' (Type s' $ tspec d)
              t                -> typ x

isInt :: (?spec::Spec, WithType a) => a -> Bool
isInt x = case tspec $ typ' x of
                 SIntSpec _ _ -> True
                 UIntSpec _ _ -> True
                 _            -> False

isBool :: (?spec::Spec, WithType a) => a -> Bool
isBool x = case tspec $ typ' x of
                BoolSpec _ -> True
                _          -> False

isPtr :: (?spec::Spec, WithType a) => a -> Bool
isPtr x = case tspec $ typ' x of
               PtrSpec _ _ -> True
               _           -> False

isArray :: (?spec::Spec, WithType a) => a -> Bool
isArray x = case tspec $ typ' x of
               ArraySpec    _ _ _ -> True
               VarArraySpec _ _   -> True
               _                  -> False

isStruct :: (?spec::Spec, WithType a) => a -> Bool
isStruct x = case tspec $ typ' x of
               StructSpec _ _ -> True
               _              -> False

isSequence :: (?spec::Spec, WithType a) => a -> Bool
isSequence x = case tspec $ typ' x of
               SeqSpec _ _ -> True
               _           -> False

isSeqContainer :: (?spec::Spec, WithType a) => a -> Bool
isSeqContainer x = case tsp of
                        SeqSpec _ _      -> True
                        StructSpec _ fs  -> any (isSeqContainer . Type sc . tspec) fs
                        ArraySpec _ t _  -> isSeqContainer (Type sc t)
                        VarArraySpec _ t -> isSeqContainer (Type sc t)
                        _                -> False
                   where Type sc tsp = typ' x
-------------------------------------------------
-- Various equivalence relations over types
-------------------------------------------------

-- Type isomorphism: types are equivalent modulo UserTypeSpec expansion
typeIso :: (?spec::Spec, WithType a, WithType b) => a -> b -> Bool
typeIso x y = 
    let Type sx tx = typ' x
        Type sy ty = typ' y
    in case (tx, ty) of
            (BoolSpec _         , BoolSpec _)         -> True
            (SIntSpec _ wx      , SIntSpec _ wy)      -> wx == wy
            (UIntSpec _ wx      , UIntSpec _ wy)      -> wx == wy
            (StructSpec _ fsx   , StructSpec _ fsy)   -> length fsx == length fsy &&
                                                         (and $ map (\(fx,fy) -> name fx == name fy && 
                                                                                 typeIso (Type sx $ tspec fx) (Type sy $ tspec fy))
                                                                    (zip fsx fsy))
            (EnumSpec _ esx     , EnumSpec _ esy)     -> sx == sy && 
                                                         length esx == length esy &&
                                                         (and $ map (\(ex,ey) -> name ex == name ey) (zip esx esy))
            (PtrSpec _ ptx      , PtrSpec _ pty)      -> typeIso (Type sx ptx) (Type sy pty)
            (ArraySpec _  atx lx, ArraySpec _ aty ly) -> typeIso (Type sx atx) (Type sy aty) &&
                                                         (let ?scope = sx in evalInt lx) == (let ?scope = sy in evalInt ly)
            (VarArraySpec _ atx , VarArraySpec _ aty) -> typeIso (Type sx atx) (Type sy aty)
            (SeqSpec _ stx      , SeqSpec _ sty)      -> typeIso (Type sx stx) (Type sy sty)
            (_                  , _)                  -> False


-- Instances of types can be assigned to each other
typeMatch :: (?spec::Spec, WithType a, WithType b) => a -> b -> Bool
typeMatch x y = 
    let Type sx tx = typ' x
        Type sy ty = typ' y
    in case (tx, ty) of
            (BoolSpec _         , BoolSpec _)         -> True
            (SIntSpec _ wx      , SIntSpec _ wy)      -> wx == wy
            (UIntSpec _ wx      , UIntSpec _ wy)      -> wx == wy
            (StructSpec _ fsx   , StructSpec _ fsy)   -> length fsx == length fsy &&
                                                         (and $ map (\(fx,fy) -> name fx == name fy && 
                                                                                 typeMatch (Type sx $ tspec fx) (Type sy $ tspec fy))
                                                                    (zip fsx fsy))
            (EnumSpec _ esx     , EnumSpec _ esy)     -> sx == sy && 
                                                         length esx == length esy &&
                                                         (and $ map (\(ex,ey) -> name ex == name ey) (zip esx esy))
            (PtrSpec _ ptx      , PtrSpec _ pty)      -> typeIso (Type sx ptx) (Type sy pty)
            (ArraySpec _  atx lx, ArraySpec _ aty ly) -> typeMatch (Type sx atx) (Type sy aty) &&
                                                         (let ?scope = sx in evalInt lx) == (let ?scope = sy in evalInt ly)
            (VarArraySpec _  atx, VarArraySpec _ aty) -> typeMatch (Type sx atx) (Type sy aty)
            (SeqSpec _  stx     , SeqSpec _ sty)      -> typeMatch (Type sx stx) (Type sy sty)
            (_                  , FlexTypeSpec _)     -> True
            (_                  , _)                  -> False


checkTypeMatch :: (?spec::Spec, WithPos a, Show a, WithType b, WithType c, MonadError String me) => a -> b -> c -> me ()
checkTypeMatch y tx ty = do
    assert (typeMatch tx ty) (pos y) $
           "Type mismatch: expected type: " ++ (showType $ typ tx) ++ ", actual type " ++ (showType $ typ ty) ++ " in " ++ show y


-- Objects of these types can be compared using == and !=
typeComparable :: (?spec::Spec, WithType a, WithType b) => a -> b -> Bool
typeComparable x y =     
    let Type sx tx = typ' x
        Type sy ty = typ' y
    in --trace ("typeComparable " ++ show x ++ " " ++ show y) $
       case (tx, ty) of
            (BoolSpec _         , BoolSpec _)         -> True
            (SIntSpec _ wx      , SIntSpec _ wy)      -> wx == wy
            (UIntSpec _ wx      , UIntSpec _ wy)      -> wx == wy
--            (UIntSpec _ _       , SIntSpec _ _)       -> True
--            (SIntSpec _ _       , UIntSpec _ _)       -> True
            (StructSpec _ fsx   , StructSpec _ fsy)   -> length fsx == length fsy &&
                                                         (and $ map (\(fx,fy) -> name fx == name fy && 
                                                                                 typeIso (Type sx $ tspec fx) (Type sy $ tspec fy))
                                                                    (zip fsx fsy))
            (EnumSpec _ esx     , EnumSpec _ esy)     -> sx == sy && 
                                                         length esx == length esy &&
                                                         (and $ map (\(ex,ey) -> name ex == name ey) (zip esx esy))
            (PtrSpec _ ptx      , PtrSpec _ pty)      -> typeIso (Type sx ptx) (Type sy pty)
            (ArraySpec _  atx lx, ArraySpec _ aty ly) -> typeMatch (Type sx atx) (Type sy aty) &&
                                                         (let ?scope = sx in evalInt lx) == (let ?scope = sy in evalInt ly)
            (VarArraySpec _  atx, VarArraySpec _ aty) -> typeMatch (Type sx atx) (Type sy aty)
            (SeqSpec _  stx     , SeqSpec _ sty)      -> typeMatch (Type sx stx) (Type sy sty)
            (_                  , _)                  -> False


typeWidth :: (?spec::Spec, WithType a) => a -> Int
typeWidth x = case tspec $ typ' x of
                   SIntSpec _ w -> w
                   UIntSpec _ w -> w
                   _            -> error $ "typeWidth: non-integral type"

typeSigned :: (?spec::Spec, WithType a) => a -> Bool
typeSigned x = case tspec $ typ' x of
                   SIntSpec _ _ -> True
                   UIntSpec _ _ -> False
                   _            -> error $ "typeSigned: non-integral type"


---------------------------------------------------------------------
-- TypeDecl dependency graph
---------------------------------------------------------------------

type TDeclGraph = G.Gr StaticSym ()

gTypeName :: (TypeDecl,Scope) -> GStaticSym
gTypeName (d,ScopeTop)        = [name d]
gTypeName (d,ScopeTemplate t) = [name t,name d]

tdeclDeps :: (?spec::Spec) => GStaticSym -> [GStaticSym]
tdeclDeps n = (\(d,s) -> typeDeps (Type s $ tspec d)) $ getTypeDecl ScopeTop n

typeDeps :: (?spec::Spec) => Type -> [GStaticSym]
typeDeps (Type s (StructSpec _ fs)) = concat $ 
    map ((\t -> case t of
                     UserTypeSpec _ n -> [gTypeName $ getTypeDecl s n]
                     _                -> typeDeps (Type s t)) . tspec)
        fs
typeDeps (Type s (UserTypeSpec _ n)) = [gTypeName $ getTypeDecl s n]
typeDeps _                    = []


-- construct dependency graph
tdeclGraph :: (?spec::Spec) => TDeclGraph
tdeclGraph = 
    let tnames = map ((\n -> [n]) . name) (specType ?spec) ++ 
                 (concat $ map (\t -> map (\d -> [name t, name d]) $ tmTypeDecl t) $ specTemplate ?spec)
        tmap = M.fromList $ zip tnames [1..]
        gnodes = foldl' (\g (t,id) -> G.insNode (id, t) g) G.empty (M.toList tmap)
    in foldl' (\g n -> foldl' (\g d -> G.insEdge (tmap M.! n, tmap M.! d, ()) g) 
                              g (tdeclDeps n))
              gnodes tnames

