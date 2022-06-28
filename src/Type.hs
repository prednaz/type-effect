{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Type where


import Data.Set as S
import Debug.Trace
import Ast
import Show
import Data.Bifunctor
import Data.Maybe
import Data.Map as M
import Control.Monad.State
import Data.Traversable
import Data.List (intercalate)

newtype FunId   = FunId Pi deriving (Eq, Ord, Show)
type Ann        = Set FunId
data TyVar      = TyVar Name Integer deriving (Eq, Show, Ord)
newtype AnnVar  = AnnVar Integer deriving (Eq, Ord, Show)
data Ty a       = FreeVar TyVar | TInt | TBool | TArrow (Ty a) a (Ty a) | TPair a (Ty a) (Ty a) deriving Show
data TyScheme a = SType (Ty a) | Forall TyVar (TyScheme a) deriving Show
type TyEnv      = Map Name (TyScheme AnnVar)
type TySubst    = (Map TyVar (Ty AnnVar), Map AnnVar AnnVar)



{-
instance Show TySubst where
  show _ = "TySubst"
-}

data Constr = Super AnnVar Ann | SuperVar AnnVar AnnVar deriving (Eq, Ord, Show)
type Constrs = Set Constr

newtype RdrName = RdrName String
data Id         = Id Name Integer

--findWithDefault :: Ord k => v -> k -> [(k, v)] -> v
--findWithDefault d k m = fromMaybe d (lookup k m)

replaceTyVar :: (TyVar -> TyVar) -> Ty a -> Ty a
replaceTyVar f (FreeVar v) = FreeVar $ f v
replaceTyVar _ TInt = TInt
replaceTyVar _ TBool = TBool
replaceTyVar f (TArrow t1 cs t2) = TArrow (replaceTyVar f t1) cs (replaceTyVar f t2)
replaceTyVar f (TPair cs t1 t2) = TPair cs (replaceTyVar f t1) (replaceTyVar f t2)

substTyVar :: TySubst -> Ty AnnVar -> Ty AnnVar
substTyVar s (FreeVar v) = findWithDefault (FreeVar v) v (fst s)
substTyVar _ TInt = TInt
substTyVar _ TBool = TBool
substTyVar s (TArrow t1 a t2) = TArrow (substTyVar s t1) (findWithDefault a a (snd s)) (substTyVar s t2)
substTyVar s (TPair a t1 t2) = TPair (findWithDefault a a (snd s)) (substTyVar s t1) (substTyVar s t2)

substTyScheme :: TySubst -> TyScheme AnnVar -> TyScheme AnnVar
substTyScheme s (SType ty)     = SType $ substTyVar s ty
substTyScheme s (Forall ty ts) = Forall ty $ substTyScheme (first (M.delete ty) s) ts

substEnv :: TySubst -> TyEnv -> TyEnv
substEnv s = fmap (substTyScheme s)

substTyAnn :: TySubst -> AnnVar -> AnnVar
substTyAnn s v = findWithDefault v v (snd s)

substTyAnnC :: TySubst -> Constr -> Constr
substTyAnnC s (Super v t) = Super (substTyAnn s v) t
substTyAnnC s (SuperVar a b) = SuperVar (substTyAnn s a) (substTyAnn s b)

substTyAnns :: TySubst -> Constrs -> Constrs
substTyAnns s = S.map (substTyAnnC s)

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

freshVar :: State Integer (Ty a)
freshVar = state $ \s -> (FreeVar $ TyVar "a" s, s + 1)

freshAnnVar :: State Integer AnnVar
freshAnnVar = state $ \s -> (AnnVar s, s + 1)

cfaInstantiate :: TyScheme a -> State Integer (Ty a)
cfaInstantiate (SType ty)    = return ty
cfaInstantiate (Forall v ts) = do
  i <- freshIndex
  replaceTyVar (freshen i v) <$> cfaInstantiate ts

freeVars :: Ty a -> Set TyVar
freeVars (FreeVar v) = S.singleton v
freeVars (TArrow t1 _ t2) = freeVars t1 `S.union` freeVars t2
freeVars _ = mempty

schemeFreeVars :: TyScheme a -> Set TyVar
schemeFreeVars (SType _)     = mempty
schemeFreeVars (Forall t ts) = S.insert t $ schemeFreeVars ts

envFreeVars :: TyEnv -> Set TyVar
envFreeVars = M.foldr (\x y -> schemeFreeVars x `S.union` y) mempty

generalise :: TyEnv -> Ty a -> TyScheme a
generalise e t = S.foldr Forall (SType t) (freeVars t `S.difference` envFreeVars e)


chk :: TyVar -> Ty a -> TySubst -> TySubst
chk a (FreeVar b) = id
chk a b           = chk' a b

chk' :: TyVar -> Ty a -> TySubst -> TySubst
chk' a (FreeVar b) s
  | a == b    = error $ show a ++ " matches " ++ show b ++ " in chk"
  | otherwise = s
chk' a (TArrow t1 _ t2) s = chk a t1 (chk a t2 s)
chk' _ _ s = s

unify :: Ty AnnVar -> Ty AnnVar -> State Integer (TySubst, Constrs)
unify TInt TInt   = return mempty
unify TBool TBool = return mempty
unify (TPair b1 t1 t2) (TPair b2 t3 t4) = do
  (a1, c1) <- subeffect b1
  (a2, c2) <- subeffect b2
  let th0 = (mempty, M.singleton a1 a2)
  (th1, c3) <- unify (substTyVar th0 t1) (substTyVar th0 t3)
  (th2, c4) <- unify (substTyVar th1 (substTyVar th0 t2)) (substTyVar th1 (substTyVar th0 t4))
  return (composeSubst th2 (composeSubst th1 th0), S.unions [c1, c2, c3, c4])
unify (TArrow t1 b1 t2) (TArrow t3 b2 t4) = do
  (a1, c1) <- subeffect b1
  (a2, c2) <- subeffect b2
  let th0 = (mempty, M.singleton a1 a2)
  (th1, c3) <- unify (substTyVar th0 t1) (substTyVar th0 t3)
  (th2, c4) <- unify (substTyVar th1 (substTyVar th0 t2)) (substTyVar th1 (substTyVar th0 t4))
  return (composeSubst th2 (composeSubst th1 th0), S.unions [c1, c2, c3, c4])
unify (FreeVar a) t = return (chk a t (M.singleton a t, mempty), mempty)
unify t (FreeVar a) = return (chk a t (M.singleton a t, mempty), mempty)
unify a b = error ("cannot unify " ++ show a ++ " ~ " ++ show b)

unify' :: Ty AnnVar -> Ty AnnVar -> TySubst
unify' TInt TInt   = mempty
unify' TBool TBool = mempty
unify' (TPair b1 t1 t2) (TPair b2 t3 t4) = composeSubst th2 (composeSubst th1 th0)
  where
    th0 = (mempty, M.singleton b1 b2)
    th1 = unify' (substTyVar th0 t1) (substTyVar th0 t3)
    th2 = unify' (substTyVar th1 (substTyVar th0 t2)) (substTyVar th1 (substTyVar th0 t4))
unify' (TArrow t1 b1 t2) (TArrow t3 b2 t4) = composeSubst th2 (composeSubst th1 th0)
  where
    th0 = (mempty, M.singleton b1 b2)
    th1 = unify' (substTyVar th0 t1) (substTyVar th0 t3)
    th2 = unify' (substTyVar th1 (substTyVar th0 t2)) (substTyVar th1 (substTyVar th0 t4))
unify' (FreeVar a) t = chk a t (M.singleton a t, mempty)
unify' t (FreeVar a) = chk a t (M.singleton a t, mempty)
unify' a b = error ("cannot unify " ++ show a ++ " ~ " ++ show b)

subeffect :: AnnVar -> State Integer (AnnVar, Constrs)
subeffect a = do
  b <- freshAnnVar
  return (b, S.singleton (SuperVar b a))


{-
subeffect :: Ty AnnVar -> State Integer (Ty AnnVar, Constrs)
subeffect (TArrow t1 a t2) = do
  b <- freshAnnVar
  return (TArrow t1 b t2, S.singleton (SuperVar b a))
subeffect t = return (t, mempty)
-}

cfaW :: TyEnv -> Expr -> State Integer (Ty AnnVar, TySubst, Constrs)
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
  (tau, th1, c1) <- cfaW e' t
  (th2, c2) <- unify tau (substTyVar th1 a2)
  let tau' = TArrow (substTyVar th2 (substTyVar th1 a1)) (substTyAnn th2 (substTyAnn th1 b)) (substTyVar th2 tau)
  let c3 = S.map (substTyAnnC th2) (S.unions [c1, c2]) `S.union` S.singleton (Super (substTyAnn th2 (substTyAnn th1 b)) (S.singleton $ FunId pi))
  let th = composeSubst th2 th1
  return (tau', th, substTyAnns th c3)
cfaW e (App t1 t2)  = do
  (tau1, th1, c1) <- cfaW e t1
  (tau2, th2, c2) <- cfaW (substEnv th1 e) t2
  a <- freshVar
  b <- freshAnnVar
  let th3 = unify' (substTyVar th2 tau1) (TArrow tau2 b a)
  let th = composeSubsts [th3, th2, th1]
  return (substTyVar th3 a, th, substTyAnns th $ c1 `S.union` c2)
cfaW e (Let x t1 t2) = do
  (tau1, th1, c1) <- cfaW e t1
  let e' = substEnv th1 e
  let e1 = M.insert x (generalise e' tau1) e'
  (tau, th2, c2) <- cfaW e1 t2
  let th = composeSubst th2 th1
  return (tau, th, substTyAnns th $ c1 `S.union` c2)
cfaW e (ITE t1 t2 t3) = do
  (tau1, th1, c1) <- cfaW e t1
  let e1 = substEnv th1 e
  (tau2, th2, c2) <- cfaW e1 t2
  let e2 = substEnv th2 e1
  (tau3, th3, c3) <- cfaW e2 t3
  (th4, c4) <- unify (substTyVar th3 (substTyVar th2 tau1)) TBool
  (th5, c5) <- unify (substTyVar th4 (substTyVar th3 tau2)) (substTyVar th4 tau3)
  let th = composeSubsts [th5, th4, th3, th2, th1]
  return (substTyVar th5 (substTyVar th4 tau3), th, substTyAnns th $ S.unions [c1, c2, c3, c4, c5])
cfaW e (Oper op t1 t2) = do
  (tau1, th1, c1) <- cfaW e t1
  (tau2, th2, c2) <- cfaW (substEnv th1 e) t2
  (th3, c3) <- unify (substTyVar th2 tau1) TInt
  (th4, c4) <- unify (substTyVar th3 tau2) TInt
  let th = composeSubsts [th4, th3, th2, th1]
  return (TInt, th, substTyAnns th $ S.unions [c1, c2, c3, c4])
cfaW e (Pair pi t1 t2) = do
  (tau1, th1, c1) <- cfaW e t1
  traceShow t1 $ return ()
  traceShow e $ return ()
  traceShow tau1 $ return ()
  (tau2, th2, c2) <- cfaW (substEnv th1 e) t2
  a <- freshAnnVar
  let th = composeSubst th2 th1
  return (TPair a (substTyVar th tau1) tau2, th, substTyAnns th $ S.insert (Super (substTyAnn th a) $ S.singleton (FunId pi)) $ c1 `S.union` c2)
cfaW e (PCase t1 x y t2) = do
  (tau1, th1, c1) <- cfaW e t1
  a1 <- freshVar
  a2 <- freshVar
  b <- freshAnnVar
  (th2, c2) <- unify (TPair b a1 a2) tau1
  let th = composeSubst th2 th1
  let e' = substEnv th e
  let e1 = M.insert x (generalise e' (substTyVar th a1)) e'
  let e2 = M.insert y (generalise e1 (substTyVar th a2)) e1
  (tau2, th3, c3) <- cfaW e2 t2
  let th' = composeSubst th3 th
  return (tau2, th', substTyAnns th' $ S.unions [c1, c2, c3])

cfaW' :: Expr -> ((Ty AnnVar, TySubst, Constrs), Integer)
cfaW' x = flip runState 0 $ cfaW mempty x

solveConstraint :: Constrs -> AnnVar -> Ann
solveConstraint cs a = S.unions $ S.map g $ S.filter f cs
  where
    f (Super b _)    = a == b
    f (SuperVar b _) = a == b
    g (Super _ s)    = s
    g (SuperVar _ v) = solveConstraint cs v -- this loops if a >= b and b >= a, we could solve this, but why?
                                            -- (only subeffecting produces SuperVar)

typeOf :: Expr -> TyScheme Ann
typeOf x = case fst $ cfaW' x of
  (t, s, cs) -> --traceShow cs $ traceShow s $ traceShow t $
                generalise mempty $ replaceAnnVar (solveConstraint cs) t

replaceAnnVar :: (AnnVar -> Ann) -> Ty AnnVar -> Ty Ann
replaceAnnVar f (TArrow t1 a t2) = TArrow (replaceAnnVar f t1) (f a) (replaceAnnVar f t2)
replaceAnnVar f (FreeVar tv) = FreeVar tv
replaceAnnVar f TInt = TInt
replaceAnnVar f TBool = TBool
replaceAnnVar f (TPair a t1 t2) = TPair (f a) (replaceAnnVar f t1) (replaceAnnVar f t2) 


pretty :: Pretty a => a -> String
pretty = pretty' False

class Pretty a where
  pretty' :: Bool -> a -> String

instance Pretty (TyScheme Ann) where
  pretty' _ (SType t)     = pretty' False t
  pretty' b (Forall t ts) = if b then "(" ++ x ++ ")" else x
    where
      x = "forall " ++ pretty' False t ++ prettyTS ts

prettyTS :: TyScheme Ann -> String
prettyTS (SType t)     = "." ++ pretty' False t
prettyTS (Forall t ts) = " " ++ pretty' False t ++ prettyTS ts

instance Pretty TyVar where
  pretty' _ (TyVar n i) = n ++ showLabel i ""

instance Pretty (Ty Ann) where
  pretty' _ (FreeVar v) = pretty' False v
  pretty' _ TInt = "Int"
  pretty' _ TBool = "Bool"
  pretty' b (TArrow t1 a t2) = if b then "(" ++ x ++ ")" else x
    where
      x =  pretty' True t1 ++ " -" ++ pretty' False a ++ "-> " ++ pretty' False t2
  pretty' b (TPair a t1 t2) = "pair" ++ pretty' False a ++ "(" ++ pretty' False t1 ++ " , " ++ pretty' False t2 ++ ")"

instance Pretty FunId where
  pretty' _ (FunId n) = show n
instance Pretty Ann where
  pretty' _ a = "{" ++ intercalate "," (pretty' False <$> S.toList a) ++ "}"