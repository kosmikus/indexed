{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module List where

import Combinators
import Typelevel
import EP
-- import Map

-- PFList :: Fin 1 >>> Fin 1
type PFListF   = K () :+: (I (TLeft Zero) :*: I (TRight Zero))
type PFList    = Fix PFListF
type PFList' a = PFList (Cons a Nil)

fromList :: [a] -> PFList' a Zero 
fromList []     = Fix (LL (K ()))
fromList (x:xs) = Fix (RR (I (JL (Z x)) :*: I (JR (fromList xs))))

toList :: PFList' a Zero -> [a]
toList (Fix (LL (K ()))) = []
toList (Fix (RR (I (JL (Z x)) :*: I (JR xs)))) = x : toList xs

fromList' :: (Cons [a] Nil) :->: PFList' a
fromList' (Z xs) = fromList xs

toList' :: POne ix -> PFList' a ix -> (Cons [a] Nil) ix
toList' PZero xs = Z (toList xs)

{-
mapList :: (a -> b) -> [a] -> [b]
mapList f xs = toList (hmap (f >>> nil) (fromList xs))
-}

type instance PF [a] = PFList' a

instance EP [a] where
  from = fromList
  to   = toList
