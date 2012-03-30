{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Map where

import Combinators
import Typelevel

-- HFunctor (pi :: i -> *) (po :: o -> *) (f :: i >>> o)
class HFunctor (f :: (* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  hmap :: (forall ix . pi ix -> r ix -> r' ix)
       -> po ix -> f pi po r ix -> f pi po r' ix

instance HFunctor (I ix) where
  hmap f po (I pi ix) = I pi (f pi ix)

instance HFunctor U where
  hmap f po U = U

instance HFunctor (K a) where
  hmap f po (K x) = K x

instance (IxRel rel, HFunctor f) =>
         HFunctor (X rel f) where
  hmap f po (X pt p a) = X pt p (hmap f (conv p po) a)

instance (HFunctor f, HFunctor g) =>
         HFunctor (f :+: g) where
  hmap f po (LL a) = LL (hmap f po a)
  hmap f po (RR a) = RR (hmap f po a)

instance (HFunctor f, HFunctor g) =>
         HFunctor (f :*: g) where
  hmap f po (a :*: b) = hmap f po a :*: hmap f po b

instance (HFunctor f) => HFunctor (Fix f) where
  hmap f po (Fix a) = Fix (hmap (f // hmap f) po a)

instance (HFunctor f, HFunctor g) =>
         HFunctor ((f :.: g) pm) where
  hmap f po (C a) = C (hmap (hmap f) po a)

instance (HFunctor f) =>
         HFunctor (Tag ix f) where
  hmap f po (Tag po' a) = Tag po' (hmap f po a)
