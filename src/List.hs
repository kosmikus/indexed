{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module List where

import Combinators
import Typelevel
import EP

-- PFList :: Fin 1 >>> Fin 1
type PFListF = K () :+: (I (TLeft Zero) :*: I (TRight Zero))
type PFList = Fix PFListF
type PFList' a = PFList POne POne (Cons a Nil)

fromList :: [a] -> PFList' a Zero 
fromList []     = Fix (LL (K ()))
fromList (x:xs) = Fix (RR (I (PLeft PZero) (JL (Z x)) :*: I (PRight PZero) (JR (fromList xs))))

toList :: PFList' a Zero -> [a]
toList (Fix (LL (K ()))) = []
toList (Fix (RR (I _ (JL (Z x)) :*: I _ (JR xs)))) = x : toList xs

fromList' :: POne ix -> (Cons [a] Nil) ix -> PFList' a ix
fromList' PZero (Z xs) = fromList xs

toList' :: POne ix -> (PFList' a ix -> (Cons [a] Nil) ix)
toList' PZero xs = Z (toList xs)

{-
mapList :: (a -> b) -> [a] -> [b]
mapList f xs = toList (hmap (f >>> nil) PZero (fromList xs))
-}

type instance PF [a] = PFList' a

instance EP [a] where
  from = fromList
  to   = toList
