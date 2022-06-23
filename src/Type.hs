{-# LANGUAGE TypeFamilies #-}

module Type where


import Data.Set as S

import Ast
import Show
import Data.Bifunctor
import Data.Maybe
import Data.Map as M
import Control.Monad.State
import Data.Traversable

newtype FunId   = FunId Pi deriving (Eq, Ord, Show)
type Ann        = Set FunId
data TyVar      = TyVar Name Integer deriving (Eq, Show, Ord)
newtype AnnVar  = AnnVar Integer deriving (Eq, Ord, Show)
data Ty         = FreeVar TyVar | TInt | TBool | TArrow Ty AnnVar Ty deriving Show
data TyScheme   = SType Ty | Forall TyVar TyScheme deriving Show
type TyEnv      = Map Name TyScheme
type TySubst    = (Map TyVar Ty, Map AnnVar AnnVar)



{-
instance Show TySubst where
  show _ = "TySubst"
-}

data Constr = Super AnnVar Ann deriving (Eq, Ord, Show)
type Constrs = Set Constr

newtype RdrName = RdrName String
data Id         = Id Name Integer

--findWithDefault :: Ord k => v -> k -> [(k, v)] -> v
--findWithDefault d k m = fromMaybe d (lookup k m)

replaceTyVar :: (TyVar -> TyVar) -> Ty -> Ty
replaceTyVar f (FreeVar v) = FreeVar $ f v
replaceTyVar _ TInt = TInt
replaceTyVar _ TBool = TBool
replaceTyVar f (TArrow t1 cs t2) = TArrow (replaceTyVar f t1) cs (replaceTyVar f t2)

substTyVar :: TySubst -> Ty -> Ty
substTyVar s (FreeVar v) = findWithDefault (FreeVar v) v (fst s)
substTyVar _ TInt = TInt
substTyVar _ TBool = TBool
substTyVar s (TArrow t1 cs t2) = TArrow (substTyVar s t1) cs (substTyVar s t2)

substTyScheme :: TySubst -> TyScheme -> TyScheme
substTyScheme s (SType ty)     = SType $ substTyVar s ty
substTyScheme s (Forall ty ts) = Forall ty $ substTyScheme (first (M.delete ty) s) ts

substEnv :: TySubst -> TyEnv -> TyEnv
substEnv s = fmap (substTyScheme s)

substTyAnn :: TySubst -> AnnVar -> AnnVar
substTyAnn s v = findWithDefault v v (snd s)

substTyAnnC :: TySubst -> Constr -> Constr
substTyAnnC s (Super v t) = Super (substTyAnn s v) t

composeSubst :: TySubst -> TySubst -> TySubst
composeSubst s''@(s, s') t''@(t, t') = (fmap (substTyVar s'') t `M.union` s, fmap (substTyAnn s'') t' `M.union` s')

composeSubsts :: [TySubst] -> TySubst
composeSubsts = Prelude.foldr composeSubst mempty

freshen :: Integer -> TyVar -> TyVar -> TyVar
freshen i (TyVar v j) x@(TyVar w k)
  | v == w, j == k    = TyVar v i
  | otherwise         = x

freshIndex :: State Integer Integer
freshIndex = state $ \s -> (s, s + 1)

freshVar :: State Integer Ty
freshVar = state $ \s -> (FreeVar $ TyVar "a" s, s + 1)

freshAnnVar :: State Integer AnnVar
freshAnnVar = state $ \s -> (AnnVar s, s + 1)

cfaInstantiate :: TyScheme -> State Integer Ty
cfaInstantiate (SType ty)    = return ty
cfaInstantiate (Forall v ts) = do
  i <- freshIndex
  replaceTyVar (freshen i v) <$> cfaInstantiate ts

freeVars :: Ty -> Set TyVar
freeVars (FreeVar v) = S.singleton v
freeVars (TArrow t1 _ t2) = freeVars t1 `S.union` freeVars t2
freeVars _ = mempty

schemeFreeVars :: TyScheme -> Set TyVar
schemeFreeVars (SType _)     = mempty
schemeFreeVars (Forall t ts) = S.insert t $ schemeFreeVars ts

envFreeVars :: TyEnv -> Set TyVar
envFreeVars = M.foldr (\x y -> schemeFreeVars x `S.union` y) mempty

generalise :: TyEnv -> Ty -> TyScheme
generalise e t = S.foldr Forall (SType t) (freeVars t `S.difference` envFreeVars e)


chk :: TyVar -> Ty -> TySubst -> TySubst
chk a (FreeVar b) = id
chk a b           = chk' a b

chk' :: TyVar -> Ty -> TySubst -> TySubst
chk' a (FreeVar b) s
  | a == b    = error $ show a ++ " matches " ++ show b ++ " in chk"
  | otherwise = s
chk' a (TArrow t1 _ t2) s = chk a t1 (chk a t2 s)
chk' _ _ s = s

unify :: Ty -> Ty -> TySubst
unify TInt TInt   = mempty
unify TBool TBool = mempty
unify (TArrow t1 b1 t2) (TArrow t3 b2 t4) = composeSubst th2 (composeSubst th1 th0)
  where
    th0 = (mempty, M.singleton b1 b2)
    th1 = unify (substTyVar th0 t1) (substTyVar th0 t3)
    th2 = unify (substTyVar th1 (substTyVar th0 t2)) (substTyVar th1 (substTyVar th0 t4))
unify (FreeVar a) t = chk a t (M.singleton a t, mempty)
unify t (FreeVar a) = chk a t (M.singleton a t, mempty)
unify a b = error ("cannot unify " ++ show a ++ " ~ " ++ show b)

cfaW :: TyEnv -> Expr -> State Integer (Ty, TySubst, Constrs)
cfaW e (Integer n) = pure (TInt, mempty, mempty)
cfaW e (Bool b) =    pure (TBool, mempty, mempty)
cfaW e (Var s) = do
  x <- cfaInstantiate (findWithDefault (error $ s ++ " not in environment " ++ show e) s e)
  return (x, mempty, mempty)
cfaW e (Fn pi x t) = do
  a1 <- freshVar
  (tau, th, c) <- cfaW (M.insert x (SType a1) e) t
  b <- freshAnnVar
  return (TArrow (substTyVar th a1) b tau, th, c `S.union` S.singleton (Super b (S.singleton $ FunId pi)))
cfaW e (Fun pi f x t) = do
  a1 <- freshVar
  a2 <- freshVar
  b <- freshAnnVar
  let e' = M.fromList [(f, SType $ TArrow a1 b a2), (x, SType a1)] `M.union` e
  (tau, th1, c) <- cfaW e' t
  let th2 = unify tau (substTyVar th1 a2)
  let tau' = TArrow (substTyVar th2 (substTyVar th1 a1)) (substTyAnn th2 (substTyAnn th1 b)) (substTyVar th2 tau)
  let c' = S.map (substTyAnnC th2) c `S.union` S.singleton (Super (substTyAnn th2 (substTyAnn th1 b)) (S.singleton $ FunId pi))
  return (tau', composeSubst th2 th1, c')
cfaW e (App t1 t2)  = do
  (tau1, th1, c1) <- cfaW e t1
  (tau2, th2, c2) <- cfaW (substEnv th1 e) t2
  a <- freshVar
  b <- freshAnnVar
  let th3 = unify (substTyVar th2 tau1) (TArrow tau2 b a)
  return (substTyVar th3 a, composeSubsts [th3, th2, th1], c1 `S.union` c2)
cfaW e (Let x t1 t2) = do
  (tau1, th1, c1) <- cfaW e t1
  let e' = substEnv th1 e
  let e1 = M.insert x (generalise e' tau1) e'
  (tau, th2, c2) <- cfaW e1 t2
  return (tau, composeSubst th2 th1, c1 `S.union` c2)
cfaW e (ITE t1 t2 t3) = do
  (tau1, th1, c1) <- cfaW e t1
  let e1 = substEnv th1 e
  (tau2, th2, c2) <- cfaW e1 t2
  let e2 = substEnv th2 e1
  (tau3, th3, c3) <- cfaW e2 t3
  let th4 = unify (substTyVar th3 (substTyVar th2 tau1)) TBool
  let th5 = unify (substTyVar th4 (substTyVar th3 tau2)) (substTyVar th4 tau3)
  return (substTyVar th5 (substTyVar th4 tau3), composeSubsts [th5, th4, th3, th2, th1], S.unions [c1, c2, c3])
cfaW e (Oper op t1 t2) = do
  (tau1, th1, c1) <- cfaW e t1
  (tau2, th2, c2) <- cfaW (substEnv th1 e) t2
  let th3 = unify (substTyVar th2 tau1) TInt
  let th4 = unify (substTyVar th3 tau2) TInt
  return (TInt, composeSubsts [th4, th3, th2, th1], c1 `S.union` c2)

cfaW' :: Expr -> ((Ty, TySubst, Constrs), Integer)
cfaW' x = flip runState 0 $ cfaW mempty x

typeOf :: Expr -> TyScheme
typeOf x = undefined


