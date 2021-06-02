{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Frontend.MethodOps(argType,
                          methLabels,
                          methFullVar,
                          methFullBody,
                          methLocalDecls,
                          methParent) where

import Data.Maybe
import Control.Monad.Except
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Tree as G

import TSLUtil
import Pos
import Name
import Frontend.NS
import Frontend.Type
import Frontend.TypeOps
import Frontend.Method
import Frontend.Template
import Frontend.TemplateOps
import Frontend.Statement
import Frontend.StatementOps
import Frontend.Spec
import Frontend.TVar

argType :: (?spec::Spec, ?scope::Scope) => Arg -> Type
argType = Type ?scope . tspec

methLabels :: (?spec::Spec) => Method -> [Ident]
methLabels meth = case methBody meth of
                       Left (mbef, maft) -> concatMap statLabels $ catMaybes [mbef, maft]
                       Right st          -> statLabels st

-- Find implementation of the method inherited from a parent
methParent :: (?spec::Spec) => Template -> Method -> Maybe (Template, Method)
methParent t m = 
    case listToMaybe $ catMaybes $ map (\t' -> objLookup (ObjTemplate t') (name m)) (tmParents t) of
         Nothing                -> Nothing
         Just (ObjMethod t' m') -> Just (t',m')


-- Complete method body, including inherited parts
methFullBody :: (?spec::Spec) => Template -> Method -> Either (Maybe Statement, Maybe Statement) Statement
methFullBody t m = 
    case methParent t m of
         Nothing      -> methBody m
         Just (t',m') -> case (methFullBody t' m', methBody m) of
                              (Left (mb',ma'), Left (mb,ma)) -> 
                                  let bef = case (mb',mb) of
                                                 (Nothing, Nothing) -> Nothing
                                                 (Just b', Just b)  -> Just $ sSeq nopos Nothing [b',b]
                                                 (Just b', Nothing) -> Just b'
                                                 (Nothing, Just b)  -> Just b
                                      aft = case (ma',ma) of
                                                 (Nothing, Nothing) -> Nothing
                                                 (Just a', Just a)  -> Just $ sSeq nopos Nothing [a,a']
                                                 (Just a', Nothing) -> Just a'
                                                 (Nothing, Just a)  -> Just a
                                  in Left (bef, aft)
                              (Left (mb',ma'), Right b)      -> Right $ sSeq nopos Nothing $ (maybeToList mb')++[b]++(maybeToList ma')
                              (Right b', Right b)            -> Right b
                              _                              -> Left (Nothing, Nothing)

methFullVar :: (?spec::Spec) => Template -> Method -> [(Template,Method,Var)]
methFullVar t m =
    map ((t, m,)) (methVar m) ++ 
    case methParent t m of
         Just (t',m') -> methFullVar t' m'
         Nothing      -> []


-- Objects declared in the method scope (arguments and local variables)
methLocalDecls :: (?spec::Spec) => Template -> Method -> [Obj]
methLocalDecls t m = map (ObjArg s) (methArg m) ++ map (\(t,m,v) -> ObjVar (ScopeMethod t m) v) (methFullVar t m)
    where s = ScopeMethod t m
