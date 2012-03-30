{-# LANGUAGE TypeFamilies #-}

module EP where

import Typelevel

type family PF t :: (* -> *)

class EP t where
  from :: t -> PF t Zero
  to   :: PF t Zero -> t

type family PF_1_1 f :: * -> * -> *

class EP_1_1 f where
  from_1_1 :: f a -> PF_1_1 f a Zero
  to_1_1   :: PF_1_1 f a Zero -> f a
