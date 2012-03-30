{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Combinators where

import Control.Applicative
import Typelevel

infixr 7 :->:
type (r :->: s) = forall ix. r ix -> s ix

-- kind i >>> o = (i -> *) -> (o -> *)

-- Identity functor, parameterized by the input index we
-- recurse on. We originally had
--
-- I :: i -> i >>> ()
--
-- indicating that I delivers one type, but in fact, we
-- can just make the output index polymorphic, saving a
-- superfluous reindexing in many cases.

-- I :: i -> i >>> o 
data I :: * -> (* -> *) -> (* -> *) where
  I :: r ix -> I ix r xi

-- Unit functor.

-- U :: i >>> o
data U :: (* -> *) -> (* -> *) where
  U :: U r ix

-- Sum of two functors.

infixr 5 :+:

-- (:+:) :: i >>> o -> i >>> o -> i >>> o
data (:+:) :: ((* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *)) where
  LL :: f r ix -> (f :+: g) r ix
  RR :: g r ix -> (f :+: g) r ix

-- Product of two functors.

infixr 6 :*:

-- (:*:) :: i >>> o -> i >>> o -> i >>> o
data (:*:) :: ((* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *)) where
  (:*:) :: f r ix -> g r ix -> (f :*: g) r ix

-- Reindexing by an arbitrary relation.

-- X :: (rel o1 o2) -> i >>> o1 -> i >>> o2
data X :: (* -> * -> *)
       -> ((* -> *) -> (* -> *))
       -> ((* -> *) -> (* -> *)) where
  X :: rel ix1 ix2 -> f r ix1 -> X rel f r ix2

class IxRel (rel :: * -> * -> *) where
  conv :: rel ix1 ix2 -> ix2 -> ix1

-- An experiment: Tagging, a special form of reindexing.
-- Tag :: o -> i >>> o -> i >>> o
data Tag :: *
         -> ((* -> *) -> (* -> *))
         -> ((* -> *) -> (* -> *)) where
  Tag :: f r ix -> Tag ix f r ix

-- Constant functor.

-- K :: * -> (i >>> o)
data K :: * -> (* -> *) -> (* -> *) where
  K :: a -> K a r ix

-- Fixed point. Note that indexed functors are
-- closed under fixed point, so other than in the
-- single-rec case, Fix does not turn a functor
-- into something else.

-- Fix :: (Either i o >>> o) -> (i >>> o)
data Fix :: ((* -> *) -> (* -> *))
         -> ((* -> *) -> (* -> *)) where
  Fix :: f (r :/: Fix f r) ix -> Fix f r ix

-- The join operator is used in the fixed point to
-- separate parameters from recursive positions.

-- (:/:) :: (i1 -> *) -> (i2 -> *) -> (Either i1 i2 -> *)
data (:/:) :: (* -> *) -> (* -> *) -> (* -> *) where
  JL :: f ix1 -> (f :/: g) (TLeft ix1)
  JR :: g ix2 -> (f :/: g) (TRight ix2)

(//) :: (r :->: r')
     -> (s :->: s')
     -> (r :/: s) :->: (r' :/: s')
(f // g) (JL x) = JL (f x)
(f // g) (JR x) = JR (g x)

-- Composition of two functors.

-- (:.:) :: (m >>> o) -> (i >>> m) -> (i >>> o)
data (:.:) :: ((* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *)) where
  C :: f (g r) ix -> (f :.: g) r ix

-- | Unlifted version of 'I'.
newtype I0 a   = I0 { unI0 :: a }

newtype I1 f a = I1 { unI1 :: f a }

-- | Unlifted version of 'K'.
newtype K0 a b = K0 { unK0 :: a }

instance Functor I0 where
  fmap f = I0 . f . unI0

instance Applicative I0 where
  pure              = I0
  (I0 f) <*> (I0 x) = I0 (f x)

instance Functor (K0 a) where
  fmap f = K0 . unK0
