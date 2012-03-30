{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Examples where

import List
-- import Pair
-- import ListPair
import AB
import AST
import Map
import Typelevel
import EP
import Rec
import Combinators

mapList :: (a -> b) -> [a] -> [b]
mapList f xs = toList (hmap (f >>> nil) PZero (fromList xs))

data K0 a b = K0 {unK0 :: a }

cataList :: forall a r . r -> (a -> r -> r) -> [a] -> r
cataList nil cons xs = unK0 (cata phi PZero (fromList xs))
  where
    phi :: POne ix -> PFListF (PEither POne POne) POne (Cons a Nil :/: K0 r) ix -> K0 r ix
    phi PZero (LL _) = K0 nil
    phi PZero (RR (I (PLeft PZero) (JL (Z x)) :*: I _ (JR (K0 y)))) = K0 (cons x y)

mapA :: A -> A
mapA a = toA (hmap nil PZero (fromA a))

mapB :: B -> B
mapB b = toB (hmap nil (PSucc PZero) (fromB b))

mapExpr :: (a -> b) -> Expr a -> Expr b
mapExpr f e = toExpr (hmap (f >>> nil) PZero (fromExpr e))

{-
mapPair :: (a -> b) -> (c -> d) -> (a,c) -> (b,d)
mapPair f g xy = toPair (hmap (f >>> g >>> nil) PZero (fromPair xy))

mapListPair :: (a -> b) -> (c -> d) -> [(a,c)] -> [(b,d)]
mapListPair f g xs = toListPair (hmap (f >>> g >>> nil) PZero (fromListPair xs))
-}

class Map_1_1 f where
  map :: (a -> b) -> f a -> f b

-- map_1_1 :: (EP_1_1 f, ) => (a -> b) -> f a -> f b
-- map_1_1 f xs = to (hmap (f >>> nil) PZero (from xs))
