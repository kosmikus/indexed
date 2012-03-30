{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Combinators where

import Typelevel

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
data I :: * -> (* -> *) -> (* -> *) -> (* -> *) -> (* -> *) where
  I :: pi ix -> r ix -> I ix pi po r xi

-- Unit

-- U :: i >>> o
data U :: (* -> *) -> (* -> *) -> (* -> *) -> (* -> *) where
  U :: U pi po r ix

-- Sum of two functors, collecting the output indices.

infixr 5 :+:

-- (:+:) :: i >>> o -> i >>> o -> i >>> o
data (:+:) :: ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  LL :: f pi po r ix -> (f :+: g) pi po r ix
  RR :: g pi po r ix -> (f :+: g) pi po r ix

-- Product of two functors, collecting the output indices.

infixr 6 :*:

-- (:*:) :: i >>> o -> i >>> o -> i >>> o
data (:*:) :: ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  (:*:) :: f pi po r ix -> g pi po r ix -> (f :*: g) pi po r ix

-- Reindexing by an arbitrary relation.

-- X :: (rel o1 o2) -> i >>> o1 -> i >>> o2
data X :: ((* -> *) -> (* -> *) -> * -> * -> *)
       -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
       -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  X :: (po' ix2 -> po ix1) -> rel po po' ix1 ix2 -> f pi po r ix1 -> X rel f pi po' r ix2

-- An experiment: Tagging, a special form of reindexing.
-- Tag :: o -> i >>> o -> i >>> o
data Tag :: *
         -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
         -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  Tag :: po ix -> f pi po r ix -> Tag ix f pi po r ix

class IxRel (rel :: (* -> *) -> (* -> *) -> * -> * -> *) where
  conv :: rel po1 po2 ix1 ix2 -> po2 ix2 -> po1 ix1

-- Sum, merging the output indices. Implemented using
-- collecting sum and reindexing.

-- (:+) :: i >>> o -> i >>> o -> i >>> o
type (f :+ g) = X FEither (f :+: g)

-- FEither :: (Either o o) -> o -> *
data FEither :: (* -> *) -> (* -> *) -> * -> * -> * where
  FL :: FEither (PEither po po) po (TLeft ix)  ix
  FR :: FEither (PEither po po) po (TRight ix) ix

instance IxRel FEither where
  conv FL = PLeft
  conv FR = PRight

-- Product, merging the output indices. Implemented using
-- collecting product and reindexing.

-- FPair :: (o,o) -> o -> *
data FPair :: (* -> *) -> (* -> *) -> * -> * -> * where
  FPair :: FPair (PPair po po) po (TPair ix ix) ix

instance IxRel FPair where
  conv FPair x = PPair x x

-- experimental
{-
unStar :: (f :* g) pi po r ix ->
          (f pi po r ix -> g pi po r ix -> rr) ->
          rr
unStar (X _ FPair (x :*: y)) k = k x y
-}



-- FSucc :: Either (Fin 1) (Fin n) -> Fin (Succ n) -> *
data FSucc :: (* -> *) -> (* -> *) -> * -> * -> * where
  FSuccL :: FSucc (PEither POne (PFin m)) (PFin (Succ m)) (TLeft Zero) Zero
  FSuccR :: FSucc (PEither POne (PFin m)) (PFin (Succ m)) (TRight n) (Succ n)

instance IxRel FSucc where
  conv FSuccL PZero     = PLeft  PZero
  conv FSuccR (PSucc p) = PRight p

fSuccL :: f pi (PEither POne (PFin n)) r (TLeft Zero) ->
          X FSucc f pi (PFin (Succ n)) r Zero
fSuccL f = X q FSuccL f
  where
    q :: (PFin (Succ n)) Zero -> (PEither POne (PFin n)) (TLeft Zero)
    q PZero = PLeft PZero

fSuccR :: f pi (PEither POne (PFin m)) r (TRight n) ->
          X FSucc f pi (PFin (Succ m)) r (Succ n)
fSuccR f = X q FSuccR f
  where
    q :: (PFin (Succ m)) (Succ n) -> (PEither POne (PFin m)) (TRight n)
    q (PSucc p) = PRight p

-- Constant functor.

-- K :: * -> (i >>> o)
data K :: * -> (* -> *) -> (* -> *) -> (* -> *) -> (* -> *) where
  K :: a -> K a pi po r ix

-- Fixed point. Note that indexed functors are
-- closed under fixed point, so other than in the
-- single-rec case, Fix does not turn a functor
-- into something else.

-- Fix :: (Either i o >>> o) -> (i >>> o)
data Fix :: ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
         -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  Fix :: f (PEither pi po) po (r :/: Fix f pi po r) ix -> Fix f pi po r ix

-- The join operator is used in the fixed point to
-- separate parameters from recursive positions.

-- (:/:) :: (i1 -> *) -> (i2 -> *) -> (Either i1 i2 -> *)
data (:/:) :: (* -> *) -> (* -> *) -> (* -> *) where
  JL :: f ix1 -> (f :/: g) (TLeft ix1)
  JR :: g ix2 -> (f :/: g) (TRight ix2)

(//) :: (forall ix1 . po1 ix1 -> r ix1 -> r' ix1)
     -> (forall ix2 . po2 ix2 -> s ix2 -> s' ix2)
     -> (PEither po1 po2) ix -> (r :/: s) ix -> (r' :/: s') ix
(f // g) (PLeft  po) (JL x) = JL (f po x)
(f // g) (PRight po) (JR x) = JR (g po x)

-- Composition of two functors.

-- (:.:) :: (m >>> o) -> (i >>> m) -> m -> (i >>> o)
data (:.:) :: ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
           -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *))
           -> (* -> *)
           -> ((* -> *) -> (* -> *) -> (* -> *) -> (* -> *)) where
  C :: f pm po (g pi pm r) ix -> (f :.: g) pm pi po r ix

