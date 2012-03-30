{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Pair where

import Combinators
import Typelevel
import EP

-- PFPair :: Fin 2 >>> Fin 1
type PFPair = I Zero :* I (Succ Zero)
type PFPair' a b = PFPair PTwo POne (Cons a (Cons b Nil))

fromPair :: (a,b) -> PFPair' a b Zero
fromPair (x,y) = I PZero (Z x) .* I (PSucc PZero) (S (Z y))

fromPair' :: POne ix -> (Cons (a,b) Nil) ix -> PFPair' a b ix
fromPair' PZero (Z xs) = fromPair xs

toPair :: PFPair' a b Zero -> (a,b)
toPair (X _ FPair (I _ (Z x) :*: I _ (S (Z y)))) = (x,y)

toPair' :: POne ix -> PFPair' a b ix -> Cons (a,b) Nil ix
toPair' PZero xs = Z (toPair xs)

type instance PF (a,b) = PFPair' a b

instance EP (a,b) where
  from = fromPair
  to   = toPair
