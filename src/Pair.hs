{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module Pair where

import Combinators
import Typelevel
import EP

-- PFPair :: Fin 2 >>> Fin 1
type PFPair      = I Zero :*: I (Succ Zero)
type PFPair' a b = PFPair (Cons a (Cons b Nil))

fromPair :: (a,b) -> PFPair' a b Zero
fromPair (x,y) = I (Z x) :*: I (S (Z y))

fromPair' :: (Cons (a,b) Nil) ix -> PFPair' a b ix
fromPair' (Z xs) = fromPair xs

toPair :: PFPair' a b Zero -> (a,b)
toPair (I (Z x) :*: I (S (Z y))) = (x,y)

toPair' :: POne ix -> PFPair' a b ix -> Cons (a,b) Nil ix
toPair' PZero xs = Z (toPair xs)

type instance PF (a,b) = PFPair' a b

instance EP (a,b) where
  from = fromPair
  to   = toPair
