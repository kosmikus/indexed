{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Examples where

import List
import Pair
import ListPair
import AB
import AST
import Map
import Typelevel
import EP
import Rec
import Combinators

mapList :: (a -> b) -> [a] -> [b]
mapList f xs = toList (hmap (f >>> nil) (fromList xs))

cataList :: forall a r. r -> (a -> r -> r) -> [a] -> r
cataList nil cons xs = unK0 (cata phi (fromList xs))
  where
    phi :: PFListF (Cons a Nil :/: K0 r) ix -> K0 r ix
    phi (LL _) = K0 nil
    phi (RR (I (JL (Z x)) :*: I (JR (K0 y)))) = K0 (cons x y)

anaList :: forall a r. (r -> Maybe (a, r)) -> r -> [a]
anaList coAlg x = toList (ana psi (K0 x))
  where
    psi :: K0 r :->: PFListF (Cons a Nil :/: K0 r)
    psi (K0 x) = case coAlg x of
                   Nothing     -> LL (K ())
                   Just (y, z) -> RR (I (JL (Z y)) :*: I (JR (K0 z)))


mapA :: A -> A
mapA a = toA (hmap nil (fromA a))

mapB :: B -> B
mapB b = toB (hmap nil (fromB b))


mapExpr :: (a -> b) -> Expr a -> Expr b
mapExpr f e = toExpr (hmap (f >>> nil) (fromExpr e))


mapPair :: (a -> b) -> (c -> d) -> (a,c) -> (b,d)
mapPair f g xy = toPair (hmap (f >>> g >>> nil) (fromPair xy))


mapListPair :: (a -> b) -> (c -> d) -> [(a,c)] -> [(b,d)]
mapListPair f g xs = toListPair (hmap (f >>> g >>> nil) (fromListPair xs))


class Map_1_1 f where
  map :: (a -> b) -> f a -> f b

-- map_1_1 :: (EP_1_1 f, ) => (a -> b) -> f a -> f b
-- map_1_1 f xs = to (hmap (f >>> nil) PZero (from xs))
