module Ast where

import Control.Monad.State.Lazy

data Op 
  = Add | Sub | Mul | Div
  deriving Eq
  
type Pi    = Integer -- For numbering lambda's etc. that can then be tracked in the analysis
type Name  = String  -- For identifier names

data Expr
  = Integer Integer
  | Bool    Bool
  | Var     Name
  | Fn      Pi   Name Expr
  | Fun     Pi   Name Name Expr
  | App     Expr Expr
  | Let     Name Expr Expr
  | ITE     Expr Expr Expr
  | Oper    Op   Expr Expr
  deriving Eq


bin :: Name -> Expr -> Expr -> Expr
bin op x y = Oper r x y where
  r = case op of
        "+" -> Add
        "-" -> Sub
        "*" -> Mul
        "/" -> Div

type LabelM = State Integer

assignLabels :: Expr -> Expr
assignLabels e = evalState (go e) 1
  where
    go :: Expr -> LabelM Expr
    go (App e1 e2)     = App <$> go e1 <*> go e2
    go (Let n e1 e2)   = Let n <$> go e1 <*> go e2
    go (ITE c t f)     = ITE <$> go c <*> go t <*> go f
    go (Oper op e1 e2) = Oper op <$> go e1 <*> go e2
    go (Fn _ n e')     = Fn <$> fresh <*> pure n <*> go e'
    go (Fun _ fn n e') = Fun <$> fresh <*> pure fn <*> pure n <*> go e'
    go x = pure x

    fresh :: LabelM Pi
    fresh = get >>= \s -> modify (+ 1) >> return s
