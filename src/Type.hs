{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Type where


import Data.Set as S
import Debug.Trace
import Ast
import Show
import Data.Bifunctor
import Data.Map as M
import Data.List as L
import Control.Monad.State
import Prelude hiding (pi)
import Data.Graph
import Data.Maybe

newtype FunId   = FunId Pi deriving (Eq, Ord, Show)
type Ann        = Set FunId
newtype AnnVar  = AnnVar Integer deriving (Eq, Ord, Show)
newtype TyVar   = TyVar Integer deriving (Eq, Show, Ord)
data TyScheme a = SType (Ty a) | Forall TyVar (TyScheme a) deriving Show
data Ty a       = FreeVar TyVar | TInt | TBool | TArrow (Ty a) a a (Ty a) | TPair a (Ty a) (Ty a) | TList (Ty a) a deriving Show
type TyEnv      = Map Name (TyScheme AnnVar)
type TySubst    = (Map TyVar (Ty AnnVar), Map AnnVar AnnVar)

data Constr = Super AnnVar Ann | SuperVar AnnVar AnnVar deriving (Eq, Ord, Show)
type Constrs = Set Constr

data Id         = Id Name Integer


substTyVar :: TySubst -> Ty AnnVar -> Ty AnnVar
substTyVar s (FreeVar v) = findWithDefault (FreeVar v) v (fst s)
substTyVar _ TInt = TInt
substTyVar _ TBool = TBool
substTyVar s (TArrow t1 a b t2) = TArrow (substTyVar s t1) (substTyAnn s a) (findWithDefault b b (snd s)) (substTyVar s t2)
substTyVar s (TPair a t1 t2) = TPair (findWithDefault a a (snd s)) (substTyVar s t1) (substTyVar s t2)
substTyVar s (TList t a) = TList (substTyVar s t) (findWithDefault a a (snd s))

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
composeSubst s''@(s, s') (t, t') = (fmap (substTyVar s'') t `M.union` s, fmap (substTyAnn s'') t' `M.union` s')

composeSubsts :: [TySubst] -> TySubst
composeSubsts = Prelude.foldr composeSubst mempty

freshVar :: State Integer (Ty a)
freshVar = state $ \s -> (FreeVar $ TyVar s, s + 1)

freshAnnVar :: State Integer AnnVar
freshAnnVar = state $ \s -> (AnnVar s, s + 1)

cfaInstantiate :: TyScheme AnnVar -> State Integer (Ty AnnVar)
cfaInstantiate (SType ty)    = return ty
cfaInstantiate (Forall v ts) = do
  vFresh <- freshVar
  substTyVar (M.singleton v vFresh, mempty) <$> cfaInstantiate ts

freeVars :: Ty a -> Set TyVar
freeVars (FreeVar v) = S.singleton v
freeVars (TArrow t1 _ _ t2) = freeVars t1 <> freeVars t2
freeVars (TPair _ t1 t2) = freeVars t1 <> freeVars t2
freeVars (TList t _) = freeVars t
freeVars _ = mempty

schemeFreeVars :: TyScheme a -> Set TyVar
schemeFreeVars (SType t)     = freeVars t
schemeFreeVars (Forall _ ts) = schemeFreeVars ts

envFreeVars :: TyEnv -> Set TyVar
envFreeVars = foldMap schemeFreeVars

generalise :: TyEnv -> Ty a -> TyScheme a
generalise e t = S.foldr Forall (SType t) (freeVars t `S.difference` envFreeVars e)


chk :: TyVar -> Ty a -> TySubst -> TySubst
chk _ (FreeVar _) = id
chk a b           = chk' a b

chk' :: TyVar -> Ty a -> TySubst -> TySubst
chk' a (FreeVar b) s
  | a == b    = error $ show a ++ " matches " ++ show b ++ " in chk"
  | otherwise = s
chk' a (TArrow t1 _ _ t2) s = chk a t1 (chk a t2 s)
chk' _ _ s = s

unify :: Ty AnnVar -> Ty AnnVar -> (TySubst, Ty AnnVar)
unify TInt TInt   = (mempty, TInt)
unify TBool TBool = (mempty, TBool)
unify (TPair b1 t1 t2) (TPair b2 t3 t4) = (composeSubsts [th2, th1, th], TPair b2 (substTyVar th2 left) right)
  where
    th = (mempty, M.singleton b1 b2)
    (th1, left)  = unify (substTyVar th t1) (substTyVar th t3)
    (th2, right) = unify (substTyVar th1 (substTyVar th t2)) (substTyVar th1 (substTyVar th t4))
unify (TArrow t1 a1 b1 t2) (TArrow t3 a2 b2 t4) = (composeSubsts [th2, th1, th], TArrow (substTyVar th2 left) a2 b2 right)
  where
    th = (mempty, M.fromList [(b1, b2), (a1, a2)])
    (th1, left)  = unify (substTyVar th t1) (substTyVar th t3)
    (th2, right) = unify (substTyVar th1 (substTyVar th t2)) (substTyVar th1 (substTyVar th t4))
unify (TList t1 a1) (TList t2 a2) = (composeSubst th1 th, TList t3 a2)
  where
    th = (mempty, M.singleton a1 a2)
    (th1, t3) = unify (substTyVar th t1) (substTyVar th t2)
unify (FreeVar a) t = (chk a t (M.singleton a t, mempty), t)
unify t (FreeVar a) = (chk a t (M.singleton a t, mempty), t)
unify a b = error ("cannot unify " ++ show a ++ " ~ " ++ show b)


subUnify :: Ty AnnVar -> Ty AnnVar -> State Integer (TySubst, Ty AnnVar, Constrs)
subUnify a b = do
  (a', c1) <- subtype a Co
  (b', c2) <- subtype b Co
  let (s, t) = unify a' b'
  return (s, t, c1 <> c2)

data Variance = Co | Contra deriving Eq
op :: Variance -> Variance
op Co = Contra
op Contra = Co

variance :: Variance -> AnnVar -> AnnVar -> Constr
variance Co     a b = SuperVar b a
variance Contra a b = SuperVar a b

subtype :: Ty AnnVar -> Variance -> State Integer (Ty AnnVar, Constrs)
subtype (TArrow t1 a b t2) v = do
  (t1', c1) <- subtype t1 (op v)
  a' <- freshAnnVar
  b' <- freshAnnVar
  (t2', c2) <- subtype t2 v
  return (TArrow t1' a' b' t2', S.insert (variance v a a') $ S.insert (variance v b b') $ c1 <> c2)
subtype (TPair a t1 t2) v = do
  b <- freshAnnVar
  (t1', c1) <- subtype t1 v
  (t2', c2) <- subtype t2 v
  return (TPair b t1' t2', S.insert (variance v a b) $ c1 <> c2)
subtype (TList t a) v = do
  b <- freshAnnVar
  (t', c) <- subtype t v
  return (TList t' b, S.insert (variance v a b) c)
subtype x _ = return (x, mempty)

tracePrint :: (Show a, Monad m) => a -> m ()
tracePrint x = traceShow x $ return ()

ctaW :: TyEnv -> Expr -> State Integer (Ty AnnVar, AnnVar, TySubst, Constrs)
ctaW _ (Integer _) = (TInt,, mempty, mempty) <$> freshAnnVar
ctaW _ (Bool _)    = (TBool,, mempty, mempty) <$> freshAnnVar
ctaW e (Var s) = do
  x <- cfaInstantiate (findWithDefault (error $ s ++ " not in environment " ++ show e) s e)
  (x,, mempty, mempty) <$> freshAnnVar
ctaW e (Fn pi x t) = do
  a1 <- freshVar
  (tau, eff, th, c) <- ctaW (M.insert x (SType a1) e) t
  b <- freshAnnVar
  o <- freshAnnVar
  return (TArrow (substTyVar th a1) b eff tau, o, th, c <> S.singleton (Super b (S.singleton $ FunId pi)))
ctaW e (Fun pi f x t) = do
  a1 <- freshVar
  a2 <- freshVar
  b <- freshAnnVar
  c <- freshAnnVar
  let e' = M.fromList [(f, SType $ TArrow a1 b c a2), (x, SType a1)] `M.union` e
  (tau, eff, th1, c1) <- ctaW e' t
  let (th2, _) = unify tau (substTyVar th1 a2)
  let tau' = TArrow (substTyVar th2 (substTyVar th1 a1)) (substTyAnn th2 (substTyAnn th1 b)) (substTyAnn th2 eff) (substTyVar th2 tau)
  let c3 = substTyAnns th2 c1 <> S.singleton (Super (substTyAnn th2 (substTyAnn th1 b)) (S.singleton $ FunId pi))
  let th' = (mempty, M.singleton c eff)
  let th = composeSubst th2 th1 -- move up and use
  o <- freshAnnVar
  return (tau', o, composeSubst th' th, c3)
ctaW e (App t1 t2)  = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (substEnv th1 e) t2
  a <- freshVar
  b <- freshAnnVar
  eff3 <- freshAnnVar
  let (th3, _) = unify (substTyVar th2 tau1) (TArrow tau2 b eff3 a)
  -- (th3, _, c3) <- subUnify (substTyVar th2 tau1) (TArrow tau2 b a)
  let th = composeSubsts [th3, th2, th1]
  eff <- freshAnnVar
  let c3 = S.fromList [SuperVar eff eff1, SuperVar eff eff2, SuperVar eff eff3, SuperVar eff b] -- overleaf
  return (substTyVar th3 a, eff, th, substTyAnns th $ c1 <> c2 <> c3)
ctaW e (Let x t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  let e' = substEnv th1 e
  let e1 = M.insert x (generalise e' tau1) e'
  (tau, eff2, th2, c2) <- ctaW e1 t2
  eff <- freshAnnVar
  let c3 = S.fromList [SuperVar eff eff1, SuperVar eff eff2]
  return (tau, eff, composeSubst th2 th1, substTyAnns th2 c1 <> c2 <> c3)
ctaW e (ITE t1 t2 t3) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  let e1 = substEnv th1 e
  (tau2, eff2, th2, c2) <- ctaW e1 t2
  let e2 = substEnv th2 e1
  (tau3, eff3, th3, c3) <- ctaW e2 t3
  (th4, _, c4) <- subUnify (substTyVar th3 (substTyVar th2 tau1)) TBool
  (th5, t', c5) <- subUnify (substTyVar th4 (substTyVar th3 tau2)) (substTyVar th4 tau3) -- embrace the <>
  let th = composeSubsts [th5, th4, th3, th2, th1]
  eff <- freshAnnVar
  let c6 = S.fromList [SuperVar eff eff1, SuperVar eff eff2, SuperVar eff eff3]
  return (t', eff, th, substTyAnns th $ S.unions [c1, c2, c3, c4, c5, c6])
ctaW e (Oper _ t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (substEnv th1 e) t2
  (th3, _, c3) <- subUnify (substTyVar th2 tau1) TInt
  (th4, _, c4) <- subUnify (substTyVar th3 tau2) TInt
  let th = composeSubsts [th4, th3, th2, th1]
  eff <- freshAnnVar
  let c5 = S.fromList [SuperVar eff eff1, SuperVar eff eff2]
  return (TInt, eff, th, substTyAnns th $ S.unions [c1, c2, c3, c4, c5])
ctaW e (Pair pi t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (substEnv th1 e) t2
  a <- freshAnnVar
  let th = composeSubst th2 th1
  eff <- freshAnnVar
  let c3 = S.fromList [SuperVar eff eff1, SuperVar eff eff2]
  return (TPair a (substTyVar th2 tau1) tau2, eff, th, substTyAnns th2 $ S.insert (Super a $ S.singleton (FunId pi)) $ c1 <> c2 <> c3)
ctaW e (PCase t1 x y t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  a1 <- freshVar
  a2 <- freshVar
  b <- freshAnnVar
  let (th2, _) = unify (TPair b a1 a2) tau1
  let th = composeSubst th2 th1
  let e' = substEnv th e
  let e1 = M.insert x (generalise e' (substTyVar th a1)) e'
  let e2 = M.insert y (generalise e1 (substTyVar th a2)) e1
  (tau2, eff2, th3, c2) <- ctaW e2 t2
  let th' = composeSubst th3 th
  eff <- freshAnnVar
  let c3 = S.fromList [SuperVar eff eff1, SuperVar eff eff2]
  return (tau2, eff, th', substTyAnns th' $ c1 <> c2 <> c3)
ctaW _ (Nil i) = do
  tau <- freshVar
  eff <- freshAnnVar
  a <- freshAnnVar
  return (TList tau a, eff, mempty, S.singleton (Super a (S.singleton $ FunId i)))
ctaW e (Cons i t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (substEnv th1 e) t2
  a <- freshAnnVar
  let (th3, tau) = unify (TList (substTyVar th2 tau1) a) tau2 -- subeffect manually
  let th = composeSubsts [th3, th2, th1]
  eff <- freshAnnVar
  let c3 = S.fromList [SuperVar eff eff1, SuperVar eff eff2, Super a (S.singleton $ FunId i)]
  return (tau, eff, th, substTyAnns th $ c1 <> c2 <> c3)
ctaW e (LCase t1 hd tl t2 t3) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  tau <- freshVar
  a <- freshAnnVar
  let (th2, _) = unify (TList tau a) tau1
  let th = composeSubst th2 th1
  let e' = substEnv th e
  let e1 = M.insert hd (generalise e' (substTyVar th tau)) e'
  let e2 = M.insert tl (generalise e1 (substTyVar th tau1)) e1
  (tau2, eff2, th3, c2) <- ctaW e2 t2
  (tau3, eff3, th4, c3) <- ctaW e t3
  (th5, tau4, c4) <- subUnify (substTyVar th4 tau2) tau3
  let th' = composeSubsts [th5, th3, th]
  eff <- freshAnnVar
  let c5 = S.fromList [SuperVar eff eff1, SuperVar eff eff2, SuperVar eff eff3]
  return (tau4, eff, th', substTyAnns th' $ c1 <> c2 <> c3 <> c4 <> c5)


ctaW' :: Expr -> ((Ty AnnVar, AnnVar, TySubst, Constrs), Integer)
ctaW' x = flip runState 0 $ ctaW mempty x

toGraph :: Constrs -> [(AnnVar, AnnVar, [AnnVar])]
toGraph cs = [(k, k, v) | (k, v) <- M.toList es]
  where
    es = S.foldr collect mempty cs

    addEdge b (Just c) = Just (b:c)
    addEdge b Nothing  = Just [b]

    collect (SuperVar a b) = M.alter (addEdge b) a
    collect _ = id

findSCC :: Eq node => node -> [[node]] -> [node]
findSCC x xss = fromMaybe [x] $ find (x `elem`) xss

solveAt :: Constrs -> AnnVar -> Ann
solveAt cs a = foldMap g cs
  where
    g (Super b s) | a == b = s
    g _           = mempty

solveBelow :: Constrs -> [[AnnVar]] -> AnnVar -> Ann
solveBelow cs ss a = foldMap (solveSCC cs ss) h
  where
    s = findSCC a ss

    f (SuperVar b c) = a == b && notElem c s
    f _              = False

    g (SuperVar _ b) = S.insert (findSCC b ss)
    g _              = undefined

    h = S.foldr g mempty $ S.filter f cs

solveSCC :: Constrs -> [[AnnVar]] -> [AnnVar] -> Ann
solveSCC cs ss s = S.unions $ (solveAt cs <$> s) ++ (solveBelow cs ss <$> s)

solveConstraints :: Constrs -> AnnVar -> Ann
solveConstraints cs a = solveSCC cs ss (findSCC a ss)
  where
    ss = flattenSCC <$> stronglyConnComp (toGraph cs)


labels :: Expr -> Ann
labels (Fn i _ x)           = S.insert (FunId i) $ labels x
labels (Fun i _ _ x)        = S.insert (FunId i) $ labels x
labels (App x1 x2)          = labels x1 <> labels x2
labels (Let _ x1 x2)        = labels x1 <> labels x2
labels (ITE x1 x2 x3)       = labels x1 <> labels x2 <> labels x3
labels (Oper _ x1 x2)       = labels x1 <> labels x2
labels (Pair i x1 x2)       = S.insert (FunId i) $ labels x1 <> labels x2
labels (PCase x1 _ _ x2)    = labels x1 <> labels x2
labels (Cons i x1 x2)       = S.insert (FunId i) $ labels x1 <> labels x2
labels (Nil i)              = S.singleton (FunId i)
labels (LCase x1 _ _ x2 x3) = labels x1 <> labels x2 <> labels x3
labels _ = mempty

constraintVars :: Constrs -> Set AnnVar
constraintVars = S.foldr h mempty
  where
    h (Super a _)    = S.insert a
    h (SuperVar a b) = S.insert a . S.insert b

typeOf :: Expr -> (TyScheme Ann, Ann)
typeOf x = case fst $ ctaW' x of
  (t, eff, _, cs) -> --traceShow cs $ traceShow s $ traceShow t $ traceShow eff
                (generalise mempty $ replaceAnnVar (solveConstraints cs) t
                , solveConstraints cs eff)

replaceAnnVar :: (AnnVar -> Ann) -> Ty AnnVar -> Ty Ann
replaceAnnVar f (TArrow t1 a b t2) = TArrow (replaceAnnVar f t1) (f a) (f b) (replaceAnnVar f t2)
replaceAnnVar _ (FreeVar tv) = FreeVar tv
replaceAnnVar _ TInt = TInt
replaceAnnVar _ TBool = TBool
replaceAnnVar f (TPair a t1 t2) = TPair (f a) (replaceAnnVar f t1) (replaceAnnVar f t2)
replaceAnnVar f (TList t a) = TList (replaceAnnVar f t) (f a)


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
  pretty' _ a = "{" ++ intercalate "," (pretty' False <$> S.toList a) ++ "}"

instance Pretty AnnVar where
  pretty' _ (AnnVar i) = "b" ++ showLabel i ""

instance Pretty (TyScheme Ann, Ann) where
  pretty' _ (t, eff) = pretty t ++ " & " ++ pretty eff
