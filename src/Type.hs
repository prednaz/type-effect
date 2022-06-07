{-# LANGUAGE TypeFamilies #-}

module Type where

import Data.Set

import Ast
import Show
import Data.Maybe
import Control.Monad.State
import GHC.Natural
import Data.Traversable

newtype FunId   = FunId Pi deriving (Eq, Ord, Show)
type Ann        = Set FunId 
data TyVar      = TyVar Name Natural deriving Show
newtype AnnVar  = AnnVar Natural deriving (Eq, Ord, Show)
data Ty         = FreeVar TyVar | TNat | TBool | TArrow Ty AnnVar Ty deriving Show
data TyScheme   = SType Ty | Forall TyVar TyScheme
type TyEnv      = [(Name, TyScheme)]
newtype TySubst = TypeSubst (TyVar -> Ty)

instance Show TySubst where
  show _ = "TySubst"

data Constr = Super AnnVar Ann deriving (Eq, Ord, Show)
type Constrs = Set Constr

newtype RdrName = RdrName String
data Id         = Id Name Natural

instance Show TyScheme where
  show _ = "TODO"

findWithDefault :: Ord k => v -> k -> [(k, v)] -> v
findWithDefault d k m = fromMaybe d (lookup k m)

replaceTyVar :: (TyVar -> TyVar) -> Ty -> Ty
replaceTyVar f (FreeVar v) = FreeVar $ f v
replaceTyVar _ TNat = TNat
replaceTyVar _ TBool = TBool
replaceTyVar f (TArrow t1 cs t2) = TArrow (replaceTyVar f t1) cs (replaceTyVar f t2)

substTyVar :: (TyVar -> Ty) -> Ty -> Ty
substTyVar f (FreeVar v) = f v
substTyVar _ TNat = TNat
substTyVar _ TBool = TBool
substTyVar f (TArrow t1 cs t2) = TArrow (substTyVar f t1) cs (substTyVar f t2)

freshen :: Natural -> TyVar -> TyVar -> TyVar
freshen i (TyVar v j) x@(TyVar w k)
  | v == w, j == k    = TyVar v i
  | v == w, otherwise = error "panic"
  | otherwise         = x

freshIndex :: State Natural Natural
freshIndex = state $ \s -> (s, s + 1)

freshVar :: State Natural Ty
freshVar = state $ \s -> (FreeVar $ TyVar "a" s, s + 1)

freshAnnVar :: State Natural AnnVar
freshAnnVar = state $ \s -> (AnnVar s, s + 1)

substitute :: TySubst -> Ty -> Ty
substitute (TypeSubst f) = substTyVar f

cfaInstantiate :: TyScheme -> State Natural Ty
cfaInstantiate (SType ty)    = return ty
cfaInstantiate (Forall v ts) = do
  i <- freshIndex
  replaceTyVar (freshen i v) <$> cfaInstantiate ts

cfaW :: TyEnv -> Expr -> State Natural (Ty, TySubst, Constrs)
cfaW e (Integer n) = pure (TNat, TypeSubst FreeVar, empty)
cfaW e (Bool b) = pure (TBool, TypeSubst FreeVar, empty)
cfaW e (Var s) = do
  x <- cfaInstantiate (findWithDefault (error $ s ++ " not in environment " ++ show e) s e)
  return (x, TypeSubst FreeVar, empty)
cfaW e (Fn pi x t) = do
  a1 <- freshVar
  (tau, theta, c) <- cfaW ((x, SType a1) : e) t
  b <- freshAnnVar
  return (TArrow (substitute theta a1) b tau, theta, c `union` singleton (Super b (singleton $ FunId pi)))
cfaW e (Fun n s str ex) = error "fun: unimplemented"
cfaW e (App ex ex') = error "fun: unimplemented"
cfaW e (Let s ex ex') = error "fun: unimplemented"
cfaW e (ITE ex ex' ex2) = error "fun: unimplemented"
cfaW e (Oper op ex ex') = error "fun: unimplemented"

cfaW' :: Expr -> ((Ty, TySubst, Constrs), Natural)
cfaW' x = flip runState 0 $ cfaW [] x

typeOf :: Expr -> TyScheme
typeOf x = undefined


