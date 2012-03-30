{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators         #-}

module Typelevel where

-- type-level Either/+
data PEither pl pr :: * -> * where
  PLeft  :: pl a -> PEither pl pr (TLeft a)
  PRight :: pr a -> PEither pl pr (TRight a)
data TLeft a  = TLeft a
data TRight b = TRight b

-- type-level (,)/*
data PPair pa pb :: * -> * where
  PPair :: pa a -> pb b -> PPair pa pb (TPair a b)
data TPair a b = TPair a b

data Zero
data Succ n

data PFin :: * -> * -> * where
  PZero :: PFin (Succ n) Zero
  PSucc :: PFin m n -> PFin (Succ m) (Succ n)

type PZero = PFin Zero
type POne  = PFin (Succ Zero)
type PTwo  = PFin (Succ (Succ Zero))

data Nil n
data Cons x xs n where
  Z :: x -> Cons x xs Zero
  S :: xs n -> Cons x xs (Succ n)

infixr >>>

(>>>) :: (x -> y) -> (forall n . xs n -> ys n) -> Cons x xs n -> Cons y ys n
(>>>) f g (Z x)  = Z (f x)
(>>>) f g (S xs) = S (g xs)

single :: Cons x Nil n -> x
single (Z x) = x

nil :: a
nil = error "impossible"

data a :=: b where
  Refl :: a :=: a

