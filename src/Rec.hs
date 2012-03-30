{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
module Rec where

import Combinators
import Typelevel
import Map

cata :: HFunctor f =>
        (f (r :/: s) :->: s) ->
        (Fix f r :->: s)
cata phi (Fix f) = phi (hmap (id // cata phi) f)

ana ::  HFunctor f =>
        (s :->: f (r :/: s)) ->
        (s :->: Fix f r)
ana psi x = Fix (hmap (id // ana psi) (psi x))
