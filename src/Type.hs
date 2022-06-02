module Type where
import Ast
import Show

data TypeScheme = TODO

instance Show TypeScheme where
  show TODO = "TODO"

typeOf :: Expr -> TypeScheme
typeOf _ = TODO
