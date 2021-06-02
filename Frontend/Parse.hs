{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, RecordWildCards, UndecidableInstances, TupleSections #-}

module Frontend.Parse (parseTSL) where

import qualified Data.Map         as M
import Text.Parsec
import qualified Text.PrettyPrint as P
import Data.Maybe
import Data.List
import Control.Monad
import System.Directory

import Util
import Frontend.Grammar
import PP
import Name
import Frontend.Spec
import Frontend.Builtin

builtinsPath = "/tmp/builtins.tsl"

-- Recursively parse TSL file and all of its imports
-- Takes a map of already parsed files and the name of the file
-- to parse
parseTSL :: FilePath -> [FilePath] -> Bool -> Bool -> IO (M.Map FilePath [SpecItem], Spec)
parseTSL f dirs dobuiltins musthavemain = do
    modules <- parseTSL' M.empty f dirs
    let spec = mkSpec $ concat $ snd $ unzip $ M.toList modules
    when (musthavemain && (isNothing $ find ((== "main")  . sname) $ specTemplate spec)) $ error "template main not found"
    -- Parse builtins
    builtins <- parseBuiltins
    return (modules, if' dobuiltins (mergeSpecs spec builtins) spec)

parseTSL' :: M.Map FilePath [SpecItem] -> FilePath -> [FilePath] -> IO (M.Map FilePath [SpecItem])
parseTSL' modules f dirs = do
    tsl <- readFile f
    --putStr tsl
    spec <- case parse grammar f tsl of
                 Left e   -> error $ show e
                 Right st -> return st
    createDirectoryIfMissing False "tmp"
    writeFile ("tmp/" ++ f ++ ".out") (P.render $ pp spec)
    -- Parse imports
    foldM (\mods imp -> do imp' <- findImport imp dirs
                           if M.member imp' mods
                              then return mods
                              else parseTSL' mods imp' dirs)
          (M.insert f spec modules) (imports spec)

parseBuiltins :: IO Spec
parseBuiltins = do
    -- write it to file system so that we can show it in the debugger
    writeFile builtinsPath builtinsStr
    (liftM mkSpec) $ case parse grammar builtinsPath builtinsStr of
                          Left  e  -> error $ show e
                          Right st -> return st

findImport :: FilePath -> [FilePath] -> IO String
findImport f dirs = do
    let dirs' = "":(map (++"/") dirs)
    match <- filterM (\d -> doesFileExist (d ++ f)) dirs'
    case match of
         [] -> error $ "File not found: " ++ f
         _  -> return $ head match ++ f

-- Extract the list of imports from parsed TSL spec
imports :: [SpecItem] -> [FilePath]
imports s = mapMaybe (\item -> case item of
                                    SpImport (Import _ (Ident _ n)) -> Just n
                                    _                               -> Nothing) s

mkSpec :: [SpecItem] -> Spec
mkSpec is = Spec templates types consts xducers
    where templates = mapMaybe (\i -> case i of 
                                           SpTemplate t -> Just t
                                           _            -> Nothing) is
          types = mapMaybe (\i -> case i of 
                                           SpType t     -> Just t
                                           _            -> Nothing) is
          consts = mapMaybe (\i -> case i of 
                                           SpConst c    -> Just c
                                           _            -> Nothing) is
          xducers = mapMaybe (\i -> case i of 
                                           SpTransducer t -> Just t
                                           _              -> Nothing) is

instance PP [SpecItem] where
    pp is = P.vcat $ map ((P.$+$ P.text "") . pp) is
