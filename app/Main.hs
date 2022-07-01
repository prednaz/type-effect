-- (C) 2013-14 Pepijn Kokke & Wout Elsinghorst
-- Modifications made Jurriaan Hage & Ivo Gabe de Wolff


module Main
  ( main
  ) where

import System.Environment (getArgs)
import Ast
import Show ()
import Type
import Parsing
import Pretty

import Path (parseRelDir, fileExtension, toFilePath, splitExtension, filename)
import Path.IO (listDir)
import Data.List (isSuffixOf)
import Data.Maybe (fromMaybe)
import Data.Foldable (traverse_)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["allExamples"] ->
      ((=<<) . traverse_) (\f -> putStrLn f *> run f *> putStrLn "") $
      allExamples
    [name] -> run name
    _ -> do
      putStrLn "Expected name of example program"
      putStrLn "Usage: stack run -- name"

run :: String -> IO ()
run name = do
  p <- parse name
  putStrLn "Expression:"
  print p
  putStrLn "Type:"
  putStrLn $ pretty $ typeOf p

-- |Parse and label program

parse :: String -> IO Expr
parse programName = do
  let fileName = "./examples/" ++ programName ++ ".fun"
  content <- readFile fileName
  return $ assignLabels $ parseExpr content

allExamples :: IO [FilePath]
allExamples =
  (fmap . fmap) toFilePath $
  (fmap . fmap) fst $
  ((=<<) . traverse) splitExtension $
  (fmap . fmap) filename $
  fmap
    (filter
      (
        fromMaybe False .
        fmap not .
        fmap ("~" `isSuffixOf`) .
        fileExtension
      )
    ) $
  fmap snd $
  listDir =<< parseRelDir "examples"
