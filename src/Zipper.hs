{-# LANGUAGE FlexibleContexts      #-}
-- {-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}

module Zipper where

import Prelude hiding (last)

import Control.Monad
import Control.Applicative
import Data.Maybe

import Combinators
import Typelevel
import Rec
import Map


-- * Context frames

-- | Abstract type of context frames. Not required for the high-level
-- navigation functions.

-- Ctx :: i >>> o -> i -> i >>> o
data family Ctx (f :: (* -> *) -> (* -> *)) :: * -> (* -> *) -> (* -> *)

data instance Ctx (K a) i r o

data instance Ctx U i r o

data instance Ctx (I i') i r o where
  CId :: Ctx (I i) i r o

data instance Ctx (X rel f) i r o2 where
  CX :: rel o1 o2 -> Ctx f i r o1 -> Ctx (X rel f) i r o2

data instance Ctx (f :+: g) i r o  = CL (Ctx f i r o)
                                   | CR (Ctx g i r o)

data instance Ctx (f :*: g) i r o  = C1 (Ctx f i r o) (g r o)
                                   | C2 (f r o) (Ctx g i r o)

data instance Ctx (f :.: g) i r o where
  CComp :: Ctx f m (g r) o -> Ctx g i r m -> Ctx (f :.: g) i r o

data instance Ctx (Tag o' f) i r o where
  CTag :: Ctx f i r o -> Ctx (Tag o f) i r o

data instance Ctx (Fix f) i r o where
  CFixL :: Ctx f (TLeft i)   (r :/: Fix f r) o -> Ctx (Fix f) i r o
  CFixR :: Ctx f (TRight i') (r :/: Fix f r) o -> Ctx (Fix f) i r i' -> Ctx (Fix f) i r o



-- * Generic navigation functions

-- | It is in general not necessary to use the generic navigation
-- functions directly. The functions listed in the ``Interface'' section
-- below are more user-friendly.

class HFunctor f => Zipper f where
  cmapA       :: Applicative a => (forall ix. r ix -> a (r' ix)) ->
                 Ctx f b r ix -> a (Ctx f b r' ix)
  fill        :: Ctx f b r ix -> r b -> f r ix
  first, last :: (forall b. r b -> Ctx f b r ix -> Maybe a)
              -> f r ix -> Maybe a
  next, prev  :: (forall b. r b -> Ctx f b r ix -> Maybe a)
              -> Ctx f b r ix -> r b -> Maybe a

instance Zipper (K a) where
  cmapA f void   = impossible void
  fill    void x = impossible void
  first f (K a)  = Nothing
  last  f (K a)  = Nothing
  next  f void x = impossible void
  prev  f void x = impossible void

instance Zipper U where
  cmapA f void   = impossible void
  fill    void x = impossible void
  first f U      = Nothing
  last  f U      = Nothing
  next  f void x = impossible void
  prev  f void x = impossible void

instance Zipper f => Zipper (Tag o' f) where
  cmapA f (CTag c)   = liftA CTag (cmapA f c)
  fill    (CTag c) x = Tag (fill c x)
  first f (Tag x)    = first (\z -> f z . CTag)   x
  last  f (Tag x)    = last  (\z -> f z . CTag)   x
  next  f (CTag c) x = next  (\z -> f z . CTag) c x
  prev  f (CTag c) x = prev  (\z -> f z . CTag) c x

instance (Zipper f, Zipper g) => Zipper (f :+: g) where
  cmapA f (CL c)   = liftA CL (cmapA f c)
  cmapA f (CR c)   = liftA CR (cmapA f c)
  fill    (CL c) x = LL (fill c x)
  fill    (CR c) y = RR (fill c y)
  first f (LL x)   = first (\z -> f z . CL) x
  first f (RR y)   = first (\z -> f z . CR) y
  last  f (LL x)   = last  (\z -> f z . CL) x
  last  f (RR y)   = last  (\z -> f z . CR) y
  next  f (CL c) x = next  (\z -> f z . CL) c x
  next  f (CR c) y = next  (\z -> f z . CR) c y
  prev  f (CL c) x = prev  (\z -> f z . CL) c x
  prev  f (CR c) y = prev  (\z -> f z . CR) c y

instance (Zipper f, Zipper g) => Zipper (f :*: g) where
  cmapA f (C1 c y)   = liftA2 C1 (cmapA f c) (hmapA f y)
  cmapA f (C2 x c)   = liftA2 C2 (hmapA f x) (cmapA f c)
  fill    (C1 c y) x = fill c x :*: y
  fill    (C2 x c) y = x :*: fill c y
  first f (x :*: y)  =
                first (\z c  -> f z (C1 c          y ))   x `mplus`
                first (\z c  -> f z (C2 x          c ))   y
  last  f (x :*: y)  =
                last  (\z c  -> f z (C2 x          c ))   y `mplus`
                last  (\z c  -> f z (C1 c          y ))   x
  next  f (C1 c y) x =
                next  (\z c' -> f z (C1 c'           y )) c x `mplus`
                first (\z c' -> f z (C2 (fill c x) c'))     y
  next  f (C2 x c) y =
                next  (\z c' -> f z (C2 x            c')) c y
  prev  f (C1 c y) x =
                prev  (\z c' -> f z (C1 c'           y )) c x
  prev  f (C2 x c) y =
                prev  (\z c' -> f z (C2 x            c')) c y `mplus`
                last  (\z c' -> f z (C1 c' (fill c y)))     x

instance Zipper (I xi) where
  cmapA f CId    = pure CId
  fill    CId  x = I x
  first f (I x)  = f x CId
  last  f (I x)  = f x CId
  next  f CId x  = Nothing
  prev  f CId x  = Nothing

instance (Zipper f, IxRel rel) => Zipper (X rel f) where
  cmapA f (CX r c) = liftA (CX r) (cmapA f c)
  fill  (CX r c) x = X r (fill c x)
  first f (X r c) = first (\z c' -> f z (CX r c')) c
  last f (X r c) = last (\z c' -> f z (CX r c')) c
  next f (CX r c) x = next (\z -> f z . (CX r)) c x
  prev f (CX r c) x = prev (\z -> f z . (CX r)) c x

instance (Zipper f, Zipper g) => Zipper (f :.: g) where
  cmapA f (CComp df_g dg) = liftA2 CComp (cmapA (hmapA f) df_g) (cmapA f dg)
  fill (CComp df_g dg) x = C (fill df_g (fill dg x))
  first f (C x) = first (\z c -> first (\y d -> f y (CComp c d)) z) x
  last  f (C x) = last  (\z c -> last  (\y d -> f y (CComp c d)) z) x
  next f (CComp df_g dg) x =
    next (\y d -> f y (CComp df_g d)) dg x `mplus`
    next (\z c -> first (\ y d -> f y (CComp c d)) z) df_g (fill dg x) 
  prev f (CComp df_g dg) x =
    prev (\y d -> f y (CComp df_g d)) dg x `mplus`
    prev (\z c -> last  (\y d -> f y (CComp c d)) z) df_g (fill dg x)


instance (Zipper f) => Zipper (Fix f) where
  cmapA f (CFixL c)   = liftA  CFixL (cmapA (f /// hmapA f) c)
  cmapA f (CFixR c d) = liftA2 CFixR (cmapA (f /// hmapA f) c) (cmapA f d)
  fill (CFixL c)   x  = Fix (fill c (JL x))
  fill (CFixR c d) x  = Fix (fill c (JR (fill d x)))
  first k (Fix x) = first (unJL k) x
  last  k (Fix x) = last  (unJR k) x
  next  k (CFixL c)   x = next (unJL k) c (JL x)
  next  k (CFixR c d) x = next (\s d' -> k s (CFixR c d')) d x `mplus`
                          next (unJL k) c (JR (fill d x))
  prev  k (CFixL c)   x = prev (unJR k) c (JL x)
  prev  k (CFixR c d) x = next (unJR k) c (JR (fill d x)) `mplus`
                          next (\s d' -> k s (CFixR c d')) d x

-- unJL is no longer partial
unJL :: Zipper f => 
        (forall b. r               b -> Ctx (Fix f) b r               ix -> Maybe a)
     -> (forall b. (r :/: Fix f r) b -> Ctx      f  b (r :/: Fix f r) ix -> Maybe a)
unJL k (JL x) c = k x (CFixL c)
unJL k (JR x) c = first (\s d -> k s (CFixR c d)) x

unJR :: Zipper f => 
        (forall b. r               b -> Ctx (Fix f) b r               ix -> Maybe a)
     -> (forall b. (r :/: Fix f r) b -> Ctx      f  b (r :/: Fix f r) ix -> Maybe a)
unJR k (JL x) c = k x (CFixL c)
unJR k (JR x) c = last (\s d -> k s (CFixR c d)) x



-- * Locations and context stacks

-- | Abstract type of locations. A location contains the current focus
-- and its context. A location is parameterized over the family of
-- datatypes and over the type of the complete value.

data Loc :: ((* -> *) -> (* -> *)) -> (* -> *) -> * -> * where
  Loc :: (Zipper f) => Fix f r ix -> Ctxs f ix r a -> Loc f r a

data Ctxs :: ((* -> *) -> (* -> *)) -> * -> (* -> *) -> * -> * where
  Empty :: Ctxs f a r a
  Push  :: Ctx f (TRight b) (r :/: Fix f r) ix -> Ctxs f ix r a -> Ctxs f b r a


-- * Contexts and locations are functors

instance Zipper f => HFunctor (Ctx f b) where
  hmapA = cmapA

instance (Zipper f) => HFunctor (Ctxs f b) where
  hmapA f Empty      = pure Empty
  hmapA f (Push c s) = liftA2 Push (hmapA (f /// hmapA f) c) (hmapA f s)

instance HFunctor (Loc phi) where
  hmapA f (Loc x s)  = liftA2 Loc (hmapA f x) (hmapA f s)


-- * Interface

-- ** Introduction

-- | Start navigating a datastructure. Returns a location that
-- focuses the entire value and has an empty context.
enter :: (Zipper f) => Fix f r ix -> Loc f r ix
enter x = Loc x Empty


-- ** Navigation
-- | Move down to the leftmost child. Returns 'Nothing' if the
-- current focus is a leaf.
down :: Loc f r ix -> Maybe (Loc f r ix)
down (Loc (Fix y) s) = first (mkLoc s) y

mkLoc :: Zipper f => Ctxs f xi r ix -> (r :/: Fix f r) b -> 
                     Ctx f b (r :/: Fix f r) xi -> Maybe (Loc f r ix)
mkLoc s (JL x) c = Nothing 
mkLoc s (JR x) c = Just (Loc x (Push c s))


-- | Move down to the rightmost child. Returns 'Nothing' if the
-- current focus is a leaf.
down' :: Loc f r ix -> Maybe (Loc f r ix)
down' (Loc (Fix y) s) = last (mkLoc s) y


-- | Move up to the parent. Returns 'Nothing' if the current
-- focus is the root.
up :: Loc f r ix -> Maybe (Loc f r ix)
up (Loc _ Empty     ) = Nothing
up (Loc x (Push c s)) = Just (Loc (Fix (fill c (JR x))) s)


-- | Move to the right sibling. Returns 'Nothing' if the current
-- focus is the rightmost sibling.
right :: Loc f r ix -> Maybe (Loc f r ix)
right (Loc x Empty     ) = Nothing
right (Loc x (Push c s)) = next (mkLoc s) c (JR x)


-- | Move to the left sibling. Returns 'Nothing' if the current
-- focus is the leftmost sibling.
left :: Loc f r ix -> Maybe (Loc f r ix)
left (Loc x Empty     ) = Nothing
left (Loc x (Push c s)) = prev (mkLoc s) c (JR x)


-- ** Derived navigation.

df :: (a -> Maybe a) -> (a -> Maybe a) -> (a -> Maybe a) -> a -> Maybe a
df d u lr l =
  case d l of
    Nothing -> df' l
    r       -> r
 where
  df' l =
    case lr l of
      Nothing -> case u l of
                   Nothing -> Nothing
                   Just l' -> df' l'
      r       -> r

-- | Move through all positions in depth-first left-to-right order.
dfnext :: Loc f r ix -> Maybe (Loc f r ix)
dfnext = df down up right

-- | Move through all positions in depth-first right-to-left order.
dfprev :: Loc f r ix -> Maybe (Loc f r ix)
dfprev = df down' up left

-- ** Elimination

-- | Return the entire value, independent of the current focus.
leave :: Loc f r ix -> (Fix f) r ix
leave (Loc x Empty) = x
leave loc           = leave (fromJust (up loc))


-- | Operate on the current focus. This function can be used to
-- extract the current point of focus.

on :: (forall xi. (Fix f) r xi -> a) -> Loc f r ix -> a
on f (Loc x _) = f x

-- | Update the current focus without changing its type.
update :: (forall xi. (Fix f) r xi -> (Fix f) r xi) -> Loc f r ix -> Loc f r ix
update f (Loc x s) = Loc (f x) s


-- * Internal functions

impossible :: a -> b
impossible x = error "impossible"
