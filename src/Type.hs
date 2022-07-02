{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Type where


import Data.Map ( findWithDefault, Map )
import Data.Set ( Set )
import qualified Data.Map as M
import qualified Data.Set as S

import Ast ( Expr(..), Name, Pi )
import Control.Monad.State
    ( runState,
      MonadState(state),
      State )
import Prelude hiding (pi)
import Data.Graph ( flattenSCC, stronglyConnComp )
import Data.Maybe ( mapMaybe )
import Data.Foldable (Foldable(fold))

newtype FunId   = FunId Pi deriving (Eq, Ord, Show)
type Ann        = Set FunId
newtype AnnVar  = AnnVar Integer deriving (Eq, Ord, Show)
newtype TyVar   = TyVar Integer deriving (Eq, Show, Ord)
-- | A @Ty a@ represents a type with type annotations of type @a@.
-- A @TArrow t1 a b t2@ is the @t1 -> t2@ function type, which may have been defined at program points in @a@, and may call functions defined at points in @b@.
-- The @TPair@ and @TList@ constructors respectively represent pairs and lists, where the @a@ annotation contains all locations they could have been created.
data Ty a       = FreeVar TyVar | TInt | TBool | TArrow (Ty a) a a (Ty a) | TPair a (Ty a) (Ty a) | TList (Ty a) a deriving Show
data TyScheme a = SType (Ty a) | Forall TyVar (TyScheme a) deriving Show
type TyEnv      = Map Name (TyScheme AnnVar)
-- | A @TySubst@ represents the composite substitution from type variables to types, and annotation variables to annotation variables.
data TySubst    = TySubst (Map TyVar (Ty AnnVar)) (Map AnnVar AnnVar)

-- | A @Constr@ represents a relation between an annotation variable and either another variable, or a program point.
-- @Ni a pi@ expresses that @pi@ is in @a@, and @Super a b@ indicates that @a@ contains @b@.
data Constr = Ni AnnVar FunId | Super AnnVar AnnVar deriving (Eq, Ord, Show)
type Constrs = Set Constr

-- | Infer the type and annotation of a given (top-level) expression.
typeOf :: Expr -> (TyScheme Ann, Ann)
typeOf x = case ctaW' x of
  (t, eff, _, cs) -> --traceShow cs $ traceShow s $ traceShow t $ traceShow eff
                (generalise mempty $ replaceAnnVar (solveConstraints cs') t'
                , solveConstraints cs' eff)
    where
      (s', cs') = simplify cs
      t' = subst s' t

-- | Run @ctaW@ on an expression.
ctaW' :: Expr -> (Ty AnnVar, AnnVar, TySubst, Constrs)
ctaW' x = fst $ runState (ctaW mempty x) 0

-- * algorithm W

-- | @ctaW@ implements algorithm W adapted to Call Tracking Analysis.
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
  return (TArrow (subst th a1) b eff tau, o, th, annNi b pi c)
ctaW e (Fun pi f x t) = do
  a1 <- freshVar
  a2 <- freshVar
  b <- freshAnnVar
  c <- freshAnnVar
  let e' = M.fromList [(f, SType $ TArrow a1 b c a2), (x, SType a1)] `M.union` e
  (tau, eff, th1, c') <- ctaW e' t
  (tau', c1) <- subtype tau Co
  let (th2, _) = unify tau' (subst th1 a2)
  let th = th2 <> th1 <> TySubst mempty (M.singleton c eff)
  let tau'' = TArrow (subst th a1) (subst th b) (subst th eff) (subst th tau')
  let c2 = subst th (annNi (subst th b) pi c')
  o <- freshAnnVar
  return (tau'', o, th, subst th $ c1 <> c2)
ctaW e (App t1 t2)  = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (subst th1 e) t2
  a <- freshVar
  b <- freshAnnVar
  eff3 <- freshAnnVar
  (tau1', c3) <- subtype tau1 Co
  (tau2', c4) <- subtype tau2 Co
  let (th3, _) = unify (subst th2 tau1') (TArrow tau2' b eff3 a)
  let th = fold [th3, th2, th1]
  (eff, c5) <- annUnion [eff1, eff2, eff3, b]
  return (subst th3 a, eff, th, subst th $ fold [c1, c2, c3, c4, c5])
ctaW e (Let x t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  let e' = genIn x tau1 (subst th1 e)
  (tau, eff2, th2, c2) <- ctaW e' t2
  let th = th2 <> th1
  (eff, c3) <- annUnion [eff1, eff2]
  return (tau, eff, th, subst th $ c1 <> c2 <> c3)
ctaW e (ITE t1 t2 t3) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  let e1 = subst th1 e
  (tau2, eff2, th2, c2) <- ctaW e1 t2
  let e2 = subst th2 e1
  (tau3, eff3, th3, c3) <- ctaW e2 t3
  (th4, _, c4) <- subUnify (subst th3 (subst th2 tau1)) TBool
  (th5, t', c5) <- subUnify (subst th4 (subst th3 tau2)) (subst th4 tau3)
  let th = fold [th5, th4, th3, th2, th1]
  (eff, c6) <- annUnion [eff1, eff2, eff3]
  return (t', eff, th, subst th $ S.unions [c1, c2, c3, c4, c5, c6])
ctaW e (Oper _ t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (subst th1 e) t2
  (th3, _, c3) <- subUnify (subst th2 tau1) TInt
  (th4, _, c4) <- subUnify (subst th3 tau2) TInt
  let th = fold [th4, th3, th2, th1]
  (eff, c5) <- annUnion [eff1, eff2]
  return (TInt, eff, th, subst th $ S.unions [c1, c2, c3, c4, c5])
ctaW e (Pair pi t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (subst th1 e) t2
  a <- freshAnnVar
  let th = th2 <> th1
  (eff, c3) <- annUnion [eff1, eff2]
  return (TPair a (subst th2 tau1) tau2, eff, th, subst th2 $ annNi (subst th a) pi $ c1 <> c2 <> c3)
ctaW e (PCase t1 x y t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  a1 <- freshVar
  a2 <- freshVar
  b <- freshAnnVar
  (tau1', c4) <- subtype tau1 Co
  let (th2, _) = unify (TPair b a1 a2) tau1'
  let th = th2 <> th1
  let e' = genIn x (subst th a1) $ genIn y (subst th a2) $ subst th e
  (tau2, eff2, th3, c2) <- ctaW e' t2
  let th' = th3 <> th
  (eff, c3) <- annUnion [eff1, eff2]
  return (tau2, eff, th', subst th' $ fold [c1, c2, c3, c4])
ctaW _ (Nil i) = do
  tau <- freshVar
  eff <- freshAnnVar
  a <- freshAnnVar
  return (TList tau a, eff, mempty, annNi a i mempty)
ctaW e (Cons i t1 t2) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  (tau2, eff2, th2, c2) <- ctaW (subst th1 e) t2
  a <- freshAnnVar
  (tau1', c4) <- subtype tau1 Co
  (tau2', c5) <- subtype tau2 Co
  let (th3, _) = unify (TList (subst th2 tau1') a) tau2'
  let th = fold [th3, th2, th1]
  a' <- freshAnnVar
  eff <- freshAnnVar
  let c3 = annNi a' i $ S.fromList [Super eff eff1, Super eff eff2, Super a' a]
  return (TList (subst th tau1') a', eff, th, subst th $ fold [c1, c2, c3, c4, c5])
ctaW e (LCase t1 hd tl t2 t3) = do
  (tau1, eff1, th1, c1) <- ctaW e t1
  tau <- freshVar
  a <- freshAnnVar
  (tau', c6) <- subtype tau Co
  (tau1', c7) <- subtype tau1 Co
  let (th2, _) = unify (TList tau' a) tau1'
  let th = th2 <> th1
  let e' = genIn hd (subst th tau') $ genIn tl (subst th tau1') $ subst th e
  (tau2, eff2, th3, c2) <- ctaW e' t2
  (tau3, eff3, th4, c3) <- ctaW e t3
  (th5, tau4, c4) <- subUnify (subst th4 tau2) tau3
  let th' = fold [th5, th3, th]
  (eff, c5) <- annUnion [eff1, eff2, eff3]
  return (tau4, eff, th', subst th' $ fold [c1, c2, c3, c4, c5, c6, c7])

-- * subtyping

-- | Unify the subtypes of the argument types.
subUnify :: Ty AnnVar -> Ty AnnVar -> State Integer (TySubst, Ty AnnVar, Constrs)
subUnify a b = do
  (a', c1) <- subtype a Co
  (b', c2) <- subtype b Co
  let (s, t) = unify a' b'
  return (s, t, c1 <> c2)

-- | Create a subtype of the given type.
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

-- -- | Create a subeffected type of a given type.
-- subtype :: Ty AnnVar -> Variance -> State Integer (Ty AnnVar, Constrs)
-- subtype (TArrow t1 a b t2) v = do
--   a' <- freshAnnVar
--   b' <- freshAnnVar
--   return (TArrow t1 a' b' t2, S.insert (variance v a a') $ S.insert (variance v b b') $ mempty)
-- subtype (TPair a t1 t2) v = do
--   b <- freshAnnVar
--   return (TPair b t1 t2, S.insert (variance v a b) $ mempty)
-- subtype (TList t a) v = do
--   b <- freshAnnVar
--   return (TList t b, S.insert (variance v a b) mempty)
-- subtype x _ = return (x, mempty)

-- | A @Variance@ tracks the polarity of locations in types.
-- For an arrow @t1 -> t2@ in positive position, @t1@ is negative, and vice versa.
data Variance = Co | Contra deriving Eq

op :: Variance -> Variance
op Co = Contra
op Contra = Co

-- | If @a@ and @b@ occur in the same location in @t1@ and @t2@ respectively,
-- return the necessary constraint to maintain @t1 <= t2@.
-- This means that if @a@ is covariant or positive, we return @a <= b@,
-- and @b <= a@ if it is contravariant or negative.
variance :: Variance -> AnnVar -> AnnVar -> Constr
variance Co     a b = Super b a
variance Contra a b = Super a b

-- * unification

-- | Unify two types, returning the substition and unified type.
unify :: Ty AnnVar -> Ty AnnVar -> (TySubst, Ty AnnVar)
unify TInt TInt   = (mempty, TInt)
unify TBool TBool = (mempty, TBool)
unify (TPair b1 t1 t2) (TPair b2 t3 t4) = (fold [th2, th1, th], TPair b2 (subst th2 left) right)
  where
    th = TySubst mempty $ M.singleton b1 b2
    (th1, left)  = unify (subst th t1) (subst th t3)
    (th2, right) = unify (subst th1 (subst th t2)) (subst th1 (subst th t4))
unify (TArrow t1 a1 b1 t2) (TArrow t3 a2 b2 t4) = (fold [th2, th1, th], TArrow (subst th2 left) a2 b2 right)
  where
    th = TySubst mempty $ M.fromList [(b1, b2), (a1, a2)]
    (th1, left)  = unify (subst th t1) (subst th t3)
    (th2, right) = unify (subst th1 (subst th t2)) (subst th1 (subst th t4))
unify (TList t1 a1) (TList t2 a2) = (th1 <> th, TList t3 a2)
  where
    th = TySubst mempty $ M.singleton a1 a2
    (th1, t3) = unify (subst th t1) (subst th t2)
unify (FreeVar a) t = (chk a t (TySubst (M.singleton a t) mempty), t)
unify t (FreeVar a) = (chk a t (TySubst (M.singleton a t) mempty), t)
unify a b = error ("cannot unify " ++ show a ++ " ~ " ++ show b)

-- | Check whether the given type variable and type are unifiable.
-- This wrapper for @chk'@ ensures that @a@ unifies with @FreeVar a@,
-- while this would not unify after stripping of a type constructor, which would 
-- create an infinite type.
chk :: TyVar -> Ty a -> TySubst -> TySubst
chk _ (FreeVar _) = id
chk a b           = chk' a b

-- | Check whether the given type variable and type are unifiable.
-- Note that @a@ cannot unify with @FreeVar a@ here, since this would indicate
-- the overall type becomes infinite.
chk' :: TyVar -> Ty a -> TySubst -> TySubst
chk' a (FreeVar b) s
  | a == b    = error $ show a ++ " matches " ++ show b ++ " in chk"
  | otherwise = s
chk' a (TArrow t1 _ _ t2) s = chk' a t1 (chk' a t2 s)
chk' a (TPair _ t1 t2) s = chk' a t1 (chk' a t2 s)
chk' a (TList t1 _) s = chk' a t1 s
chk' _ TInt s = s
chk' _ TBool s = s

-- * helpers

-- | Create a fresh type variable.
freshVar :: State Integer (Ty a)
freshVar = state $ \s -> (FreeVar $ TyVar s, s + 1)

-- | Create a fresh annotation variable.
freshAnnVar :: State Integer AnnVar
freshAnnVar = state $ \s -> (AnnVar s, s + 1)

-- | For @as@, create an annotation variable @a@ and the constraints expressing that @a@ contains the union of @as@.  
annUnion :: [AnnVar] -> State Integer (AnnVar, Constrs)
annUnion as = do
    a <- freshAnnVar
    return (a, S.fromList $ Super a <$> as)

-- | @annNi a pi@ inserts the constraint expressing that @pi@ is in @a@.
annNi :: AnnVar -> Pi -> Constrs -> Constrs
annNi a pi = S.insert (Ni a (FunId pi))

-- | Generalise and insert a variable into an environment.
genIn :: Name -> Ty AnnVar -> TyEnv -> TyEnv
genIn x t e = M.insert x (generalise e t) e

-- | Instatiate a type scheme to a type by replacing all bound variables with fresh ones.
cfaInstantiate :: TyScheme AnnVar -> State Integer (Ty AnnVar)
cfaInstantiate (SType ty)    = return ty
cfaInstantiate (Forall v ts) = do
  vFresh <- freshVar
  subst (TySubst (M.singleton v vFresh) mempty) <$> cfaInstantiate ts

-- | Generalise a type to a type scheme by quantifying all variables which appear freely in the type and are unbound in the environment.
generalise :: TyEnv -> Ty a -> TyScheme a
generalise e t = S.foldr Forall (SType t) (freeVars t `S.difference` envFreeVars e)

envFreeVars :: TyEnv -> Set TyVar
envFreeVars = foldMap schemeFreeVars

schemeFreeVars :: TyScheme a -> Set TyVar
schemeFreeVars (SType t)     = freeVars t
schemeFreeVars (Forall t ts) = S.delete t $ schemeFreeVars ts

freeVars :: Ty a -> Set TyVar
freeVars (FreeVar v) = S.singleton v
freeVars (TArrow t1 _ _ t2) = freeVars t1 <> freeVars t2
freeVars (TPair _ t1 t2) = freeVars t1 <> freeVars t2
freeVars (TList t _) = freeVars t
freeVars _ = mempty

-- * substituting

{- | @Substitute a@ states that for each @s :: TySubst@, there is a meaningful substitution function @subst s :: a -> a@.
In particular @subst@ should obey the identity laws

@subst mempty = id@

@subst (TySubst (M.singleton a (FreeVar a)) mempty) = id@

@subst (TySubst mempty (M.singleton a a)) = id@

and idempotence

@subst a . subst a = subst a@

(We could narrow down the description further with alpha-equivalence lemmas (e.g. injective substitutions are bijections, and preserve alpha-equivalence both ways),
but this is left as an exercise to the reader.)
-}

class Substitute a where
  subst :: TySubst -> a -> a

-- | @substitute x s@ is the base case for most substitutions, replacing @x@ with its substitution if it is in @s@, and returning @x@ otherwise.
substitute :: Ord a => a -> Map a a -> a
substitute a = findWithDefault a a

instance Substitute (Ty AnnVar) where
  subst (TySubst l _) (FreeVar v) = findWithDefault (FreeVar v) v l
  subst _ TInt = TInt
  subst _ TBool = TBool
  subst s@(TySubst _ r) (TArrow t1 a b t2) = TArrow (subst s t1) (substitute a r) (substitute b r) (subst s t2)
  subst s@(TySubst _ r) (TPair a t1 t2) = TPair (substitute a r) (subst s t1) (subst s t2)
  subst s@(TySubst _ r) (TList t a) = TList (subst s t) (substitute a r)

-- | Notably, the @TyScheme@ instance is the only substitution which alters the substition as it is passed down,
-- removing substitutions on variables which are bound to quantifiers.
instance Substitute (TyScheme AnnVar) where
  subst s (SType ty)                 = SType $ subst s ty
  subst (TySubst l r) (Forall ty ts) = Forall ty $ subst (TySubst (M.delete ty l) r) ts

instance Substitute TyEnv where
  subst s = fmap (subst s)

instance Substitute AnnVar where
  subst (TySubst _ r) v = substitute v r

instance Substitute Constr where
  subst s (Ni v t)    = Ni (subst s v) t
  subst s (Super a b) = Super (subst s a) (subst s b)

instance (Ord a, Substitute a) => Substitute (Set a) where
  subst s = S.map (subst s)

instance Semigroup TySubst where
  s''@(TySubst s s') <> (TySubst t t') = TySubst (fmap (subst s'') t `M.union` s) (fmap (subst s'') t' `M.union` s')

-- | The @TySubst@ monoid has multiplication as substitution composition,
-- satisfying @subst (s2 <> s1) x = subst s2 $ subst s1 x@.
instance Monoid TySubst where
  mempty = TySubst mempty mempty

-- * constraints solving

-- | Return the substitution and simplified constraint set, formed by removing all cyclic components and substituting all variables in such components to a representative.
simplify :: Constrs -> (TySubst, Constrs)
simplify cs = (s, cs')
  where
    ss = flattenSCC <$> stronglyConnComp (toGraph cs)
    f x = TySubst mempty $ M.fromList [(y, head x) | y <- tail x]
    s = foldMap f ss
    cs' = deloop $ subst s cs

-- | Convert a set of constraints to the constraint graph,
-- in which a directed edge @a->b@ indicates a subset relation @a <= b@.
toGraph :: Constrs -> [(AnnVar, AnnVar, [AnnVar])]
toGraph cs = [(k, k, v) | (k, v) <- M.toList es]
  where
    es = S.foldr collect mempty cs

    addEdge b (Just c) = Just (b:c)
    addEdge b Nothing  = Just [b]

    collect (Super a b) = M.alter (addEdge b) a
    collect _ = id

-- | Remove all constraint loops of the form @Super a a@.
deloop :: Constrs -> Constrs
deloop = S.fromList . mapMaybe f . S.toList
  where
    f x@(Super a b)
      | a == b    = Nothing
      | otherwise = Just x
    f x = Just x

-- | Greedily solve a set of constraints for the least solution.
-- Loops when the constraints contain a cyclic component.
solveConstraints :: Constrs -> AnnVar -> Ann
solveConstraints cs a = S.unions $ S.map g $ S.filter f cs
  where
    f (Ni b _)       = a == b
    f (Super b _) = a == b
    
    g (Ni _ s)       = S.singleton s
    g (Super _ v) = solveConstraints cs v

replaceAnnVar :: (AnnVar -> Ann) -> Ty AnnVar -> Ty Ann
replaceAnnVar f (TArrow t1 a b t2) = TArrow (replaceAnnVar f t1) (f a) (f b) (replaceAnnVar f t2)
replaceAnnVar _ (FreeVar tv) = FreeVar tv
replaceAnnVar _ TInt = TInt
replaceAnnVar _ TBool = TBool
replaceAnnVar f (TPair a t1 t2) = TPair (f a) (replaceAnnVar f t1) (replaceAnnVar f t2)
replaceAnnVar f (TList t a) = TList (replaceAnnVar f t) (f a)
