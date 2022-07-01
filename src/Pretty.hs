{-# LANGUAGE FlexibleInstances #-}

module Pretty where

import Type
    ( Ty(..), TyScheme(..), TyVar(..), AnnVar(..), Ann, FunId(..) )
import Show (showLabel)
import Data.List (intercalate)
import Data.Foldable (Foldable(toList))

pretty :: Pretty a => a -> String
pretty = pretty' False

class Pretty a where
  pretty' :: Bool -> a -> String

instance Pretty a => Pretty (TyScheme a) where
  pretty' _ (SType t)     = pretty' False t
  pretty' b (Forall t ts) = if b then "(" ++ x ++ ")" else x
    where
      x = "forall " ++ pretty' False t ++ prettyTS ts

prettyTS :: Pretty a => TyScheme a -> String
prettyTS (SType t)     = "." ++ pretty' False t
prettyTS (Forall t ts) = " " ++ pretty' False t ++ prettyTS ts

instance Pretty TyVar where
  pretty' _ (TyVar i) = "a" ++ showLabel i ""

instance Pretty a => Pretty (Ty a) where
  pretty' _ (FreeVar v) = pretty' False v
  pretty' _ TInt = "Int"
  pretty' _ TBool = "Bool"
  pretty' b (TArrow t1 a a' t2) = if b then "(" ++ x ++ ")" else x
    where
      x =  pretty' True t1 ++ " -" ++ pretty' False a ++ ";" ++ pretty' False a' ++ "-> " ++ pretty' False t2
  pretty' _ (TPair a t1 t2) = "pair" ++ pretty' False a ++ "(" ++ pretty' False t1 ++ " , " ++ pretty' False t2 ++ ")"
  pretty' b (TList t a) = if b then "(" ++ x ++ ")" else x
    where
      x = pretty' True t ++ " list" ++ pretty' False a

instance Pretty FunId where
  pretty' _ (FunId n) = show n
instance Pretty Ann where
  pretty' _ a = "{" ++ intercalate "," (pretty' False <$> toList a) ++ "}"

instance Pretty AnnVar where
  pretty' _ (AnnVar i) = "b" ++ showLabel i ""

instance Pretty (TyScheme Ann, Ann) where
  pretty' _ (t, eff) = pretty t ++ " & " ++ pretty eff
