{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EmptyAlg where

import Combinators
import Typelevel

class Empty a where
  empty :: Bool -> a

class HEmpty (f :: (* -> *) -> (* -> *)) where
  hempty :: (K0 Bool :->: f (r :/: K0 Bool))

instance HEmpty (I ix) where
  hempty b = I undefined

instance HEmpty U where
  hempty b = U

instance Empty a => HEmpty (K a) where
  hempty (K0 b) = K (empty b)

instance (HEmpty f, HEmpty g) => HEmpty (f :+: g) where
  hempty (K0 True)  = LL (hempty (K0 True))
  hempty (K0 False) = RR (hempty (K0 False))

instance (HEmpty f, HEmpty g) => HEmpty (f :*: g) where
  hempty b = hempty b :*: hempty b

instance (HEmpty f) => HEmpty (Fix f) where
  hempty b = Fix (hempty b)

{-
instance (HEmpty f, HEmpty g) => HEmpty (f :.: g) where
  hempty b = C (hempty b)
-}

instance (HEmpty f) => HEmpty (Tag ix f) where
  hempty b = undefined
