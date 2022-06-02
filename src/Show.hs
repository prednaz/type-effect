module Show where

import Ast

showLabel :: Integer -> ShowS
showLabel label = showString $ "\ESC[93m" ++ reverse (go label) ++ "\ESC[0m"
  where
    go :: Integer -> String
    go x
      | x < 0     = error "Negative label"
      | r == 0    = subscript !! fromIntegral m : ""
      | otherwise = subscript !! fromIntegral m : go r
      where
        (r, m) = x `divMod` 10
    subscript = "₀₁₂₃₄₅₆₇₈₉"

instance Show Expr where
  showsPrec _       (Integer i)     = shows i
  showsPrec _       (Bool True)     = showString "true"
  showsPrec _       (Bool False)    = showString "false"
  showsPrec _       (Var x)         = showString x
  showsPrec context (Fn pi x e)     = showParen (context > 0) $
                                        showString "fn" . showLabel pi
                                        . showString (" " ++ x ++ " =>\n")
                                        . indent (showsPrec 0 e)
  showsPrec context (Fun pi f x e)  = showParen (context > 0) $
                                        showString "fun" . showLabel pi
                                        . showString (" " ++ f ++ " " ++ x ++ " =>\n")
                                        . indent (showsPrec 0 e)
  showsPrec context (App e1 e2)     = showParen (context > 10) $
                                        showsPrec 10 e1 . showString " " . showsPrec 11 e2
  showsPrec context (Let x e1 e2)   = showParen (context > 0) $
                                        showString ("let " ++ x ++ " =\n")
                                        . indent (showsPrec 0 e1)
                                        . showString "in\n"
                                        . indent (showsPrec 0 e2)
  showsPrec context (ITE c t f)     = showParen (context > 0) $
                                        showString "if"
                                        . indent (showsPrec 0 c)
                                        . showString "then"
                                        . indent (showsPrec 0 t)
                                        . showString "else"
                                        . indent (showsPrec 0 f)
  showsPrec context (Oper op e1 e2) = showParen (context > prec) $
                                        showsPrec prec e1
                                        . showString " "
                                        . shows op
                                        . showString " "
                                        . showsPrec (prec + 1) e2
    where
      prec = case op of
        Add -> 6
        Sub -> 6
        Mul -> 7
        Div -> 7

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Div = "/"

indent :: ShowS -> ShowS
indent s = showString $ unlines $ map ("  " ++) $ lines $ s ""
