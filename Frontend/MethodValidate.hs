{-# LANGUAGE ImplicitParams, FlexibleContexts, TupleSections #-}

module Frontend.MethodValidate(validateMeth) where

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
import Frontend.TypeValidate
import Frontend.Method
import Frontend.MethodOps
import Frontend.Template
import Frontend.TemplateOps
import Frontend.Statement
import Frontend.StatementOps
import Frontend.StatementValidate
import Frontend.Spec
import Frontend.TVar

-- Local names are unique and do not override template-level names
validateMethNS :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
validateMethNS t m = do
    uniqNames (\n -> "Identifier " ++ n ++ " declared multiple times in method " ++ sname m) 
              (methLocalDecls t m)


-- Check if the method overrides a derived declaration and, if so, 
-- make sure that method category, the number and types of arguments, 
-- and return types match
methCheckOverride :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
methCheckOverride t m = do
   case methParent t m of
        Nothing      -> do mapM (validateTypeSpec (ScopeTemplate t) . tspec) (methArg m)
                           mapM (validateTypeSpec2 (ScopeTemplate t) . tspec) (methArg m)
                           case methRettyp m of 
                                Just rt -> do validateTypeSpec (ScopeTemplate t) rt
                                              validateTypeSpec2 (ScopeTemplate t) rt
                                Nothing -> return () 
        Just (_,m')  -> do
            assert (methCat m' == methCat m) (pos m) $ 
                   "Method " ++ sname m ++ " was declared as " ++ (show $ methCat m') ++ " at " ++ spos m' ++
                   " but is redefined as " ++ (show $ methCat m) ++ " at " ++ spos m
            assert (methRettyp m' == methRettyp m) (pos m) $ 
                   "Method " ++ sname m ++ " was declared with return type " ++ (show $ methRettyp m') ++ " at " ++ spos m' ++
                   " but is redefined as " ++ (show $ methRettyp m) ++ " at " ++ spos m
            assert ((length $ methArg m') == (length $ methArg m)) (pos m) $ 
                   "Method " ++ sname m ++ " was declared with " ++ (show $ length $ methArg m') ++ " arguments at " ++ spos m' ++
                   " but is redefined with " ++ (show $ length $ methArg m) ++ " arguments at " ++ spos m
            mapM (\((a1,a2),id) -> do assert (name a1 == name a2) (pos a2) $ 
                                             "Argument " ++ show id ++ " of method " ++ sname m ++ " was declared with name " ++ sname a1 ++ " at " ++ spos a1 ++
                                             " but is redefined as " ++ sname a2 ++ " at " ++ spos a2
                                      assert (argDir a1 == argDir a2 && (tspec a1 == tspec a2)) (pos a1) $ 
                                             "Argument " ++ sname a1 ++ " was declared as " ++ show (argDir a1) ++ " " ++ show (tspec a1) ++ " at " ++ spos a1 ++
                                             " but is redefined as " ++ show (argDir a2) ++ " " ++ show (tspec a2) ++ " at " ++ spos a2)
                 (zip (zip (methArg m') (methArg m)) [(1::Int)..])
            return ()



validateMeth :: (?spec::Spec, MonadError String me) => Template -> Method -> me ()
validateMeth t m = do
    methCheckOverride t m
    validateMethNS t m
    let ?scope = ScopeMethod t m
        ?privoverride = False
    mapM (\a -> case tspec a of
                     StructSpec _ _ -> err (pos $ tspec a) "Inline struct declaration is illegal in method argument" -- because then there is no way to pass such an argument by value
                     _              -> return ())
         $ methArg m
    case methParent t m of
         Just (t',m') -> case (methBody m', methBody m) of
                              (Right _, Left _)   -> err (pos m) "Complete method body is required in overloaded method declaration"
                              _                   -> return ()

         Nothing      -> return ()
    case methFullBody t m of 
         Left (mb,ma) -> do {mapM (validateStat ?scope) (catMaybes [mb,ma]); return()}
         Right b      -> do validateStat ?scope b
                            assert (not $ (isJust $ methRettyp m) && (not $ statReturns b)) (pos m) 
                                   $ "Method " ++ show ?scope ++ " can terminate without returning a value"
