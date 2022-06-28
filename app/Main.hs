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

main :: IO ()
main = do
  args <- getArgs
  case args of
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

  
