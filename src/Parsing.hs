-- (C) 2013 Pepijn Kokke & Wout Elsinghorst
-- Adapted by Jurriaan Hage

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
module Parsing where

import Ast

import Prelude hiding ( abs, sum )
import Text.ParserCombinators.UU
import Text.ParserCombinators.UU.Utils
import Text.ParserCombinators.UU.Idioms (iI,Ii (..))
import Text.ParserCombinators.UU.BasicInstances (Parser,pSym)

-- * Top-Level Parsers

parseExpr :: String -> Expr
parseExpr = runParser "stdin" pExpr

-- * Parsing the FUN language
pExpr :: Parser Expr
pExpr = (pFn <|> pFun <|> pITE <|> pLet <|> pPair <|> pPCase <|> pCons <|> pLCase) <<|> pBin
  where
  
  -- literal expressions
  pLit = Integer <$> pInteger
     <|> Bool True  <$ pSymbol "true"
     <|> Bool False <$ pSymbol "false"
     <|> Nil 0 <$ pSymbol "Nil"
    
  -- atomic expressions
  pAtom = pLit
     <<|> Var <$> pIdent
     <<|> pParens pExpr
  
  -- simple expressions
  pFn,pFun,pLet,pITE, pPair, pPCase, pCons, pLCase :: Parser Expr
  pFn     = iI (Fn 0) "fn" pIdent "=>" pExpr Ii -- Default Pi to 0
  pFun    = iI (Fun 0) "fun" pIdent pIdent "=>" pExpr Ii -- Dito
  pLet    = iI Let "let" pIdent "=" pExpr "in" pExpr Ii
  pITE    = iI ITE "if" pExpr "then" pExpr "else" pExpr Ii
  pPair   = iI (Pair 0) "Pair" "(" pExpr "," pExpr ")" Ii
  pPCase  = iI PCase "pcase" pExpr "of" "Pair" "(" pIdent "," pIdent ")" "=>" pExpr Ii
  pCons   = iI (Cons 0) "Cons" "(" pExpr "," pExpr ")" Ii
  pLCase  = iI LCase "lcase" pExpr "of" "Cons" "(" pIdent "," pIdent ")" "=>" pExpr Ii
   
  -- chained expressions
  pApp = pChainl_ng (App <$ pSpaces) pAtom
  pBin = pChainl_ng (bin <$> pOper) pApp
  
pIdent,pConst,pOper :: Parser Name
pIdent = lexeme $ (:) <$> pLower <*> pMany (pLetter <|> pDigit <|> pUnderscore)
pConst = lexeme $ (:) <$> pUpper <*> pMany (pLetter <|> pDigit <|> pUnderscore)
pOper  = lexeme $ pSome $ pAnySym "*+/-"

pUnderscore :: Parser Char
pUnderscore = pSym '_'

-- * Recognising more list structures with separators

pFoldr2Sep :: IsParser p => (a -> b -> b, b) -> p a1 -> p a -> p b
pFoldr2Sep alg@(op,_e) sep p = must_be_non_empties "pFoldr2Sep" sep p pfm
  where pfm = op <$> p <*> pFoldr1 alg (sep *> p)

pList2Sep :: IsParser p => p a1 -> p a -> p [a]
pList2Sep s p = must_be_non_empties "pListSep" s p (pFoldr2Sep list_alg s p)
