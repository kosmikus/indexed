{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module ListPair where

import Combinators
import Typelevel
import EP
import List
import Pair
import Map

-- PFListPair :: Fin 2 >>> Fin 1
type PFListPair      = (PFList :.: PFPair)
type PFListPair' a b = PFListPair (Cons a (Cons b Nil))

fromListPair :: [(a,b)] -> PFListPair' a b Zero
fromListPair xs = C (hmap fromPair' (fromList xs))

fromListPair' :: (Cons [(a,b)] Nil) ix -> PFListPair' a b ix
fromListPair' (Z xs) = fromListPair xs

toListPair :: PFListPair' a b Zero -> [(a,b)]
toListPair (C xs) = toList (hmap (toPair' undefined) xs)

toListPair' :: POne ix -> PFListPair' a b ix -> (Cons [(a,b)] Nil) ix
toListPair' PZero xs = Z (toListPair xs)

-- type instance PF [(a,b)] = PFListPair' a b

{-
instance EP [(a,b)] where
  from = fromListPair
  to   = toListPair
-}
