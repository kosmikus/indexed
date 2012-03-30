{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Map where

import Combinators
import Typelevel
import Control.Applicative

-- HFunctor (f :: i >>> o)
class HFunctor (f :: (* -> *) -> (* -> *)) where
  hmapA :: (Applicative a)
        => (forall ix. r ix -> a (r' ix)) -> f r ix -> a (f r' ix)

instance HFunctor (I ix) where
  hmapA f (I ix) = liftA I (f ix)

instance HFunctor U where
  hmapA f U = pure U

instance HFunctor (K a) where
  hmapA f (K x) = pure (K x)

instance (HFunctor f) => HFunctor (X rel f) where
  hmapA f (X r a) = liftA (X r) (hmapA f a)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
  hmapA f (LL a) = liftA LL (hmapA f a)
  hmapA f (RR a) = liftA RR (hmapA f a)

instance (HFunctor f, HFunctor g) => HFunctor (f :*: g) where
  hmapA f (a :*: b) = liftA2 (:*:) (hmapA f a) (hmapA f b)

(///) :: (Applicative a) => 
         (forall ix. r ix -> a (r' ix))
      -> (forall ix. s ix -> a (s' ix))
      -> (r :/: s) ix -> a ((r' :/: s') ix)
(f /// g) (JL x) = liftA JL (f x)
(f /// g) (JR x) = liftA JR (g x)

instance (HFunctor f) => HFunctor (Fix f) where
  hmapA f (Fix a) = liftA Fix (hmapA (f /// hmapA f) a)

instance (HFunctor f, HFunctor g) => HFunctor (f :.: g) where
  hmapA f (C a) = liftA C (hmapA (hmapA f) a)

instance (HFunctor f) => HFunctor (Tag ix f) where
  hmapA f (Tag a) = liftA Tag (hmapA f a)

-- | 'hmap' is defined in terms of 'hmapA'
hmap :: (HFunctor f) => (r :->: r') -> f r :->: f r'
hmap f = unI0 . hmapA (I0 . f)

-- | 'hmapM' is defined in terms of 'hmapA'
hmapM :: (HFunctor f, Monad m)
      => (forall ix. r ix -> m (r' ix)) -> f r ix -> m (f r' ix)
hmapM f = unwrapMonad . hmapA (WrapMonad . f)
