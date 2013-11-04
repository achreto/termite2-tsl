{-# LANGUAGE ImplicitParams, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, TupleSections, TypeSynonymInstances, FlexibleInstances #-}

module NS(Scope(..),
          WithScope(..),
          isFunctionScope,
          isTemplateScope,
          Type(Type),
          WithType(..),
          lookupGlobal,
          lookupTemplate, checkTemplate, getTemplate, 
          lookupTypeDecl, checkTypeDecl, getTypeDecl,
          lookupTerm    , checkTerm    , getTerm,
          lookupMethod  , checkMethod  , getMethod,
          lookupGoal    , checkGoal    , getGoal,
          lookupWire    , checkWire    , getWire,
          lookupRelation, checkRelation, getRelation,
          Obj(..), objLookup, objGet, isObjMutable,
          specNamespace) where

import Control.Monad.Error
import Data.List
import Data.Maybe
import Text.PrettyPrint

import Util hiding(name,trace)
import PP
import TSLUtil
import Pos
import Name
import Template
import Process
import Method
import {-# SOURCE #-} MethodOps
import Relation
import TVar
import Const
import Type
import Spec
import Expr

data Scope = ScopeTop
           | ScopeTemplate {scopeTm::Template}
           | ScopeMethod   {scopeTm::Template, scopeMeth::Method}
           | ScopeProcess  {scopeTm::Template, scopeProc::Process}
           | ScopeRelation {scopeTm::Template, scopeRel ::Relation}

instance Eq Scope where
    (==) ScopeTop              ScopeTop              = True
    (==) (ScopeTemplate t1)    (ScopeTemplate t2)    = name t1 == name t2
    (==) (ScopeMethod t1 m1)   (ScopeMethod t2 m2)   = name t1 == name t2 && name m1 == name m2
    (==) (ScopeProcess t1 p1)  (ScopeProcess t2 p2)  = name t1 == name t2 && name p1 == name p2
    (==) (ScopeRelation t1 r1) (ScopeRelation t2 r2) = name t1 == name t2 && name r1 == name r2
    (==) _                     _                     = False

instance Ord Scope where
    compare ScopeTop              ScopeTop              = EQ
    compare ScopeTop              _                     = LT
    compare (ScopeTemplate t1)    (ScopeTemplate t2)    = compare (name t1) (name t2)
    compare (ScopeTemplate _)     ScopeTop              = GT
    compare (ScopeTemplate _)     _                     = LT
 
    compare (ScopeMethod t1 m1)   (ScopeMethod t2 m2)   = case compare (name t1) (name t2) of
                                                               EQ -> compare (name m1) (name m2)
                                                               c  -> c
    compare (ScopeMethod _ _)     ScopeTop              = GT
    compare (ScopeMethod _ _)     (ScopeTemplate _)     = GT
    compare (ScopeMethod _ _)     _                     = LT
 
    compare (ScopeProcess t1 p1)  (ScopeProcess t2 p2)  = case compare (name t1) (name t2) of
                                                               EQ -> compare (name p1) (name p2)
                                                               c  -> c
    compare (ScopeProcess _ _)    ScopeTop              = GT
    compare (ScopeProcess _ _)    (ScopeTemplate _)     = GT
    compare (ScopeProcess _ _)    (ScopeMethod _ _)     = GT
    compare (ScopeProcess _ _)    _                     = LT

    compare (ScopeRelation t1 r1) (ScopeRelation t2 r2) = case compare (name t1) (name t2) of
                                                               EQ -> compare (name r1) (name r2)
                                                               c  -> c
    compare (ScopeRelation _ _)   _                     = GT

class WithScope a where
    scope :: a -> Scope

isFunctionScope :: Scope -> Bool
isFunctionScope (ScopeMethod _ m) = methCat m == Function
isFunctionScope _                 = False

isTemplateScope :: Scope -> Bool
isTemplateScope (ScopeTemplate _) = True
isTemplateScope _                 = False


data Type = Type Scope TypeSpec

instance WithScope Type where
    scope (Type s _) = s

instance Show Scope where
    show ScopeTop             = "[top scope]"
    show (ScopeTemplate tm)   = sname tm
    show (ScopeMethod   tm m) = sname tm ++ "::" ++ sname m
    show (ScopeProcess  tm p) = sname tm ++ "::" ++ sname p
    show (ScopeRelation tm r) = sname tm ++ "::" ++ sname r

instance WithTypeSpec Type where
    tspec (Type _ t) = t

instance (?spec::Spec) => PP Type where
    pp t = case tspec t of
                UserTypeSpec _ n    -> let (d,s) = getTypeDecl (scope t) n
                                       in case s of
                                               ScopeTop         -> text $ sname d
                                               ScopeTemplate tm -> text (sname tm) <> text "::" <> text (sname d)
                StructSpec _   fs   -> text "struct" <+> 
                                       (braces $ nest' $ vcat $ map ((<> semi) . (\f -> pp (Type (scope t) (tspec f)) <+> pp (name f))) fs)
                PtrSpec _      pt   -> pp (Type (scope t) pt) <> char '*'
                ArraySpec _    at l -> pp (Type (scope t) at) <> (brackets $ pp l)
                _                   -> pp $ tspec t

instance (?spec::Spec) => Show Type where
    show = render . pp

class WithType a where
    typ :: a -> Type

instance WithType Type where
    typ = id


-- TSL specification objects

data Obj = ObjSpec
         | ObjTemplate Template
         | ObjPort     Template Port
         | ObjInstance Template Instance
         | ObjProcess  Template Process
         | ObjMethod   Template Method
         | ObjVar      Scope    Var
         | ObjGVar     Template GVar
         | ObjWire     Template Wire
         | ObjArg      Scope    Arg
         | ObjRArg     Scope    RArg
         | ObjType              Type
         | ObjTypeDecl Scope    TypeDecl
         | ObjConst    Scope    Const
         | ObjEnum     Type     Enumerator
         | ObjGoal     Template Goal
         | ObjRelation Template Relation

instance WithPos Obj where
    pos ObjSpec             = error $ "Requesting position of ObjSpec"
    pos (ObjTemplate   t)   = pos t
    pos (ObjPort     _ p)   = pos p
    pos (ObjInstance _ i)   = pos i
    pos (ObjProcess  _ p)   = pos p
    pos (ObjMethod   _ m)   = pos m
    pos (ObjVar      _ v)   = pos v
    pos (ObjGVar     _ v)   = pos v
    pos (ObjWire     _ w)   = pos w
    pos (ObjArg      _ a)   = pos a
    pos (ObjRArg     _ a)   = pos a
    pos (ObjType       t)   = pos $ tspec t
    pos (ObjTypeDecl _ t)   = pos t
    pos (ObjConst    _ c)   = pos c
    pos (ObjEnum     _ e)   = pos e
    pos (ObjGoal     _ g)   = pos g
    pos (ObjRelation _ r)   = pos r
    atPos _ = error $ "Not implemented: atPos Obj"

instance WithScope Obj where
    scope ObjSpec           = error $ "requesting scope of ObjSpec"
    scope (ObjTemplate _)   = ScopeTop
    scope (ObjPort t _)     = ScopeTemplate t
    scope (ObjInstance t _) = ScopeTemplate t
    scope (ObjProcess t _)  = ScopeTemplate t
    scope (ObjMethod t _)   = ScopeTemplate t
    scope (ObjVar s _)      = s
    scope (ObjGVar t _)     = ScopeTemplate t
    scope (ObjWire t _)     = ScopeTemplate t
    scope (ObjArg s _)      = s
    scope (ObjRArg s _)     = s
    scope (ObjType t)       = scope t
    scope (ObjTypeDecl s _) = s
    scope (ObjConst s _)    = s
    scope (ObjEnum t _)     = scope t
    scope (ObjGoal t _)     = ScopeTemplate t
    scope (ObjRelation t _) = ScopeTemplate t
    
instance WithName Obj where
    name ObjSpec           = error $ "requesting name of ObjSpec"
    name (ObjTemplate t)   = name t
    name (ObjPort     _ p) = name p
    name (ObjInstance _ i) = name i
    name (ObjProcess  _ p) = name p
    name (ObjMethod   _ m) = name m
    name (ObjVar      _ v) = name v
    name (ObjGVar     _ v) = name v
    name (ObjWire     _ w) = name w
    name (ObjArg      _ a) = name a
    name (ObjRArg     _ a) = name a
    name (ObjType       _) = error $ "requesting name of a TypeSpec"
    name (ObjTypeDecl _ t) = name t
    name (ObjConst    _ c) = name c
    name (ObjEnum     _ e) = name e
    name (ObjGoal     _ g) = name g
    name (ObjRelation _ r) = name r

instance (?spec::Spec) => WithType Obj where
    typ (ObjTemplate   _) = error $ "requesting type of ObjTemplate"
    typ (ObjPort     _ p) = Type ScopeTop $ TemplateTypeSpec (pos $ getTemplate $ portTemplate p) $ portTemplate p
    typ (ObjInstance _ i) = Type ScopeTop $ TemplateTypeSpec (pos $ getTemplate $ instTemplate i) $ instTemplate i
    typ (ObjProcess  _ _) = error $ "requesting type of ObjProcess"
    typ (ObjMethod   _ _) = error $ "requesting type of ObjMethod"
    typ (ObjVar      s v) = Type s $ tspec v
    typ (ObjGVar     t v) = Type (ScopeTemplate t) (tspec v)
    typ (ObjWire     t w) = Type (ScopeTemplate t) (tspec w)
    typ (ObjArg      s a) = Type s $ tspec a
    typ (ObjRArg     s a) = Type s $ tspec a
    typ (ObjType       t) = t
    typ (ObjTypeDecl _ _) = error $ "requesting type of ObjTypeDecl"
    typ (ObjConst    s c) = Type s $ tspec c
    typ (ObjEnum     t _) = t
    typ (ObjGoal     _ _) = error $ "requesting type of ObjGoal"
    typ (ObjRelation _ _) = error $ "requesting type of ObjRelation"

instance (?spec::Spec) => WithTypeSpec Obj where
    tspec = tspec . typ

-- True if the value of the object can change at run time
isObjMutable :: Obj -> Bool
isObjMutable ObjSpec            = False
isObjMutable (ObjTemplate _)    = False
isObjMutable (ObjPort _ _)      = False
isObjMutable (ObjInstance _ _)  = False
isObjMutable (ObjProcess _ _)   = False
isObjMutable (ObjMethod _ _)    = False
isObjMutable (ObjVar _ _)       = True
isObjMutable (ObjGVar _ _)      = True
isObjMutable (ObjWire _ _)      = True
isObjMutable (ObjArg _ _)       = True
isObjMutable (ObjRArg _ _)      = False
isObjMutable (ObjType _)        = False
isObjMutable (ObjTypeDecl _ _)  = False
isObjMutable (ObjConst _ _)     = False
isObjMutable (ObjEnum _ _)      = False
isObjMutable (ObjGoal _ _)      = False
isObjMutable (ObjRelation _ _)  = False

objLookup :: (?spec::Spec) => Obj -> Ident -> Maybe Obj
objLookup ObjSpec n = listToMaybe $ catMaybes $ [t,d,c,e]
    where s = ScopeTop
          d = fmap (ObjTypeDecl s)   $ find ((== n) . name) (specType ?spec)
          c = fmap (ObjConst    s)   $ find ((== n) . name) (specConst ?spec)
          t = fmap ObjTemplate       $ find ((== n) . name) (specTemplate ?spec)
          e = fmap (uncurry ObjEnum) $ find ((== n) . name . snd) (concatMap (\d' -> case tspec d' of
                                                                                          EnumSpec _ es -> map (Type s (tspec d'),) es
                                                                                          _             -> []) $ 
                                                                             specType ?spec)

objLookup (ObjTemplate t) n = listToMaybe $ catMaybes $ [p,v,w,i,pr,m,d,c,r,e,g,par]
    where -- search for the name in the local scope
          s = ScopeTemplate t
          p  = fmap (ObjPort     t) $ find ((== n) . name) (tmPort t)
          v  = fmap (ObjGVar     t) $ find ((== n) . name) (tmVar t)
          w  = fmap (ObjWire     t) $ find ((== n) . name) (tmWire t)
          i  = fmap (ObjInstance t) $ find ((== n) . name) (tmInst t)
          pr = fmap (ObjProcess  t) $ find ((== n) . name) (tmProcess t)
          m  = fmap (ObjMethod   t) $ find ((== n) . name) (tmMethod t) 
          d  = fmap (ObjTypeDecl s) $ find ((== n) . name) (tmTypeDecl t)
          c  = fmap (ObjConst    s) $ find ((== n) . name) (tmConst t)
          r  = fmap (ObjRelation t) $ find ((== n) . name) (tmRelation t)
          e  = fmap (uncurry ObjEnum) $ find ((== n) . name . snd) (concatMap (\d' -> case tspec d' of
                                                                                           EnumSpec _ es -> map (Type s (tspec d'),) es
                                                                                           _             -> []) $ 
                                                                              tmTypeDecl t)
          g = fmap (ObjGoal      t) $ find ((== n) . name) (tmGoal t)
          -- search parent templates
          par = listToMaybe $ catMaybes $ map (\d' -> objLookup (ObjTemplate $ getTemplate $ drvTemplate d') n) (tmDerive t)

objLookup (ObjPort _ p)     n = case objLookup ObjSpec (portTemplate p) of
                                     Just o@(ObjTemplate _)  -> objLookup o n
                                     Nothing                 -> Nothing
objLookup (ObjInstance _ i) n = case objLookup ObjSpec (instTemplate i) of
                                     Just o@(ObjTemplate _)  -> objLookup o n
                                     Nothing                 -> Nothing
objLookup (ObjProcess t p)  n = fmap (ObjVar (ScopeProcess t p)) $ find ((== n) . name) (procVar p)

objLookup (ObjMethod t m)   n = listToMaybe $ catMaybes $ [v,a]
    where v = fmap (\(t',m',v') -> ObjVar (ScopeMethod t' m') v') $ find (\(_,_,v') -> name v' == n) (methFullVar t m)
          a = fmap (ObjArg (ScopeMethod t m)) $ find ((== n) . name) (methArg m)

objLookup (ObjVar s v)      n = objLookup (ObjType $ Type s                 (tspec v)) n
objLookup (ObjGVar t v)     n = objLookup (ObjType $ Type (ScopeTemplate t) (tspec v)) n
objLookup (ObjWire t w)     n = objLookup (ObjType $ Type (ScopeTemplate t) (tspec w)) n
objLookup (ObjArg s a)      n = objLookup (ObjType $ Type s                 (tspec a)) n
objLookup (ObjRArg s a)     n = objLookup (ObjType $ Type s                 (tspec a)) n
objLookup (ObjTypeDecl s t) n = objLookup (ObjType $ Type s                 (tspec t)) n

objLookup (ObjType (Type s (StructSpec _ fs))) n = fmap (ObjType . Type s . tspec) $ find ((==n) . name) fs

objLookup (ObjType (Type _ (TemplateTypeSpec _ tn))) n = case objLookup ObjSpec tn of
                                                              Just o@(ObjTemplate _) -> objLookup o n
                                                              Nothing                -> Nothing
objLookup (ObjType (Type s (UserTypeSpec _ tn))) n = case lookupTypeDecl s tn of
                                                          Just (d,s') -> objLookup (ObjTypeDecl s' d) n
                                                          Nothing     -> Nothing

objLookup (ObjRelation t r) n = fmap (ObjRArg (ScopeRelation t r)) $ find ((== n) . name) (relArg r)
objLookup _                 _ = Nothing

objGet :: (?spec::Spec) => Obj -> Ident -> Obj
objGet o n = fromJustMsg ("objLookup " ++ sname o ++ " " ++ show n ++ " failed" ++
                          case o of 
                               ObjTemplate t -> "\n" ++ show t
                               _ -> "") $ objLookup o n

objLookupPath :: (?spec::Spec) => Obj -> [Ident] -> Maybe Obj
objLookupPath o []     = Just o
objLookupPath o (n:ns) = case objLookup o n of
                              Nothing -> Nothing
                              Just o' -> objLookupPath o' ns

-- Lookup identifier visible in the local scope
lookupIdent :: (?spec::Spec) => Scope -> Ident -> Maybe Obj
lookupIdent ScopeTop n          = objLookup ObjSpec n
lookupIdent (ScopeTemplate t) n = listToMaybe $ catMaybes [tm,global]
    where tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n
lookupIdent (ScopeMethod t m) n = listToMaybe $ catMaybes [local,tm,global]
    where local  = objLookup (ObjMethod t m) n
          tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n
lookupIdent (ScopeProcess t p) n = listToMaybe $ catMaybes [local,tm,global]
    where local  = objLookup (ObjProcess t p) n
          tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n
lookupIdent (ScopeRelation t r) n = listToMaybe $ catMaybes [local,tm,global]
    where local  = objLookup (ObjRelation t r) n
          tm     = objLookup (ObjTemplate t) n
          global = objLookup ObjSpec n

-- Lookup path from the local scope
lookupPath :: (?spec::Spec) => Scope -> [Ident] -> Maybe Obj
lookupPath s (n:ns) = case lookupIdent s n of
                           Nothing -> Nothing
                           Just o  -> objLookupPath o ns

-- Lookup name in the global namespace
lookupGlobal :: (?spec::Spec) => [Ident] -> Maybe Obj
lookupGlobal ns = objLookupPath ObjSpec ns

lookupTemplate :: (?spec::Spec) => Ident -> Maybe Template
lookupTemplate n = case objLookup ObjSpec n of
                        Just (ObjTemplate t) -> Just t
                        _                    -> Nothing
getTemplate :: (?spec::Spec) => Ident -> Template
getTemplate n = fromJustMsg ("getTemplate failed: " ++ show n) $ lookupTemplate n

checkTemplate :: (?spec::Spec, MonadError String me) => Ident -> me (Template)
checkTemplate n = do
    case lookupTemplate n of
         Nothing -> err (pos n) $ "Unknown template name: " ++ show n
         Just t  -> return t

-- Type lookup

lookupTypeLocal :: (?spec::Spec) => Scope -> Ident -> Maybe TypeDecl
lookupTypeLocal ScopeTop          n = find ((==n) . name) (specType ?spec)
lookupTypeLocal (ScopeTemplate t) n = find ((==n) . name) (tmTypeDecl t)

lookupTypeDecl :: (?spec::Spec) => Scope -> StaticSym -> Maybe (TypeDecl,Scope)
lookupTypeDecl ScopeTop [n]            = fmap (,ScopeTop) $ lookupTypeLocal ScopeTop n
lookupTypeDecl ScopeTop (n:[n'])       = case objLookup ObjSpec n of
                                              Just (ObjTemplate t) -> fmap (,ScopeTemplate t) $ lookupTypeLocal (ScopeTemplate t) n'
                                              Nothing -> Nothing
lookupTypeDecl s@(ScopeTemplate _) [n] = case lookupTypeLocal s n of
                                              Nothing -> fmap (,ScopeTop) $ lookupTypeLocal ScopeTop n
                                              Just t  -> Just (t, s)
lookupTypeDecl (ScopeTemplate _)   ns  = lookupTypeDecl ScopeTop ns
lookupTypeDecl (ScopeMethod t _)   ns  = lookupTypeDecl (ScopeTemplate t) ns
lookupTypeDecl (ScopeProcess t _)  ns  = lookupTypeDecl (ScopeTemplate t) ns
lookupTypeDecl (ScopeRelation t _) ns  = lookupTypeDecl (ScopeTemplate t) ns
lookupTypeDecl _                 _     = Nothing

checkTypeDecl :: (?spec::Spec, MonadError String me ) => Scope -> StaticSym -> me (TypeDecl,Scope)
checkTypeDecl s n = do
    case lookupTypeDecl s n of
       Nothing -> err (pos n) $ "Unknown type: " ++ (show n)
       Just t  -> return t


getTypeDecl :: (?spec::Spec) => Scope -> StaticSym -> (TypeDecl,Scope)
getTypeDecl s = fromJustMsg "getTypeDecl: type not found" . lookupTypeDecl s

-- Term lookup
-- A term is either a local name, which corresponds to any object in the local or
-- containing scope, or a global name (more than one ::-separated identifiers), which
-- must refer to a constant or enum name.
lookupTerm :: (?spec::Spec) => Scope -> StaticSym -> Maybe Obj

lookupTerm s [n] = 
    case lookupIdent s n of
         Just (ObjGoal _ _) -> Nothing
         mt                 -> mt

lookupTerm _ ns = 
    case lookupGlobal ns of
         Just o@(ObjConst _ _) -> Just o
         Just o@(ObjEnum  _ _) -> Just o
         _                     -> Nothing

checkTerm :: (?spec::Spec, MonadError String me) => Scope -> StaticSym -> me Obj
checkTerm s n = case lookupTerm s n of 
                     Nothing -> err (pos n) $ "Unknown term " ++ show n
                     Just t  -> return t

getTerm :: (?spec::Spec) => Scope -> StaticSym -> Obj
getTerm s n = fromJustMsg ("getTerm " ++ show s ++ " " ++ show n ++ ": term lookup failed\n" {-++ show ?spec-}) $ lookupTerm s n 

-- Method lookup
lookupMethod :: (?spec::Spec) => Scope -> MethodRef -> Maybe (Template, Method)
lookupMethod s (MethodRef _ p) = case lookupPath s p of
                                      Just (ObjMethod t m) -> Just (t,m)
                                      _                    -> Nothing

checkMethod :: (?spec::Spec, MonadError String me) => Scope -> MethodRef -> me (Template, Method)
checkMethod s m = case lookupMethod s m of
                       Just x  -> return x
                       Nothing -> err (pos m) $ "Unknown method " ++ show m

getMethod :: (?spec::Spec) => Scope -> MethodRef -> (Template, Method)
getMethod s m = fromJustMsg ("getMethod " ++ show s ++ " " ++ show m ++ ": method not found " ++ "\n" ++ (show ?spec)) $ lookupMethod s m

-- Goal lookup
lookupGoal :: (?spec::Spec) => Scope -> Ident -> Maybe Goal
lookupGoal s n = case lookupPath s [n] of
                      Just (ObjGoal _ g) -> Just g
                      _                  -> Nothing

checkGoal :: (?spec::Spec, MonadError String me) => Scope -> Ident -> me Goal
checkGoal s n = case lookupGoal s n of
                     Just g  -> return g
                     Nothing -> err (pos n) $ "Unknown goal " ++ show n

getGoal :: (?spec::Spec) => Scope -> Ident -> Goal
getGoal s n = fromJustMsg "getGoal: goal not found" $ lookupGoal s n

-- Wire lookup
lookupWire :: (?spec::Spec) => Scope -> Ident -> Maybe Wire
lookupWire s n = case lookupPath s [n] of
                      Just (ObjWire _ w) -> Just w
                      _                  -> Nothing

checkWire :: (?spec::Spec, MonadError String me) => Scope -> Ident -> me Wire
checkWire s n = case lookupWire s n of
                     Just w  -> return w
                     Nothing -> err (pos n) $ "Unknown wire " ++ show n

getWire :: (?spec::Spec) => Scope -> Ident -> Wire
getWire s n = fromJustMsg "getWire: wire not found" $ lookupWire s n

-- Relation lookup

lookupRelation :: (?spec::Spec) => Scope -> Ident -> Maybe (Template, Relation)
lookupRelation s n = case lookupPath s [n] of
                          Just (ObjRelation t r) -> Just (t,r)
                          _                      -> Nothing

checkRelation :: (?spec::Spec, MonadError String me) => Scope -> Ident -> me (Template, Relation)
checkRelation s n = case lookupRelation s n of
                         Just (t,r) -> return (t,r)
                         Nothing    -> err (pos n) $ "Unknown relation " ++ show n

getRelation :: (?spec::Spec) => Scope -> Ident -> (Template, Relation)
getRelation s n = fromJustMsg "getRelation: relation not found" $ lookupRelation s n


specNamespace :: (?spec::Spec) => [Obj]
specNamespace = map ObjTemplate (specTemplate ?spec) ++ 
                map (ObjTypeDecl ScopeTop) (specType ?spec) ++ 
                map (ObjConst    ScopeTop) (specConst ?spec) ++ 
                (concatMap (\d -> case tspec d of
                                       EnumSpec _ es -> map (ObjEnum (Type ScopeTop $ tspec d)) es
                                       _             -> []) (specType ?spec))
