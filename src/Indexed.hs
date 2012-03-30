{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Indexed where

data Sum a b = L a | R b

data Sum1 (a :: i1 -> *) (b :: i2 -> *) :: Sum i1 i2 -> * where
  LL :: a i -> Sum1 a b (L i)
  RR :: b i -> Sum1 a b (R i)


data Code i o = UNIT
              | SUM (Code i o) (Code i o)
              | PROD (Code i o) (Code i o)
--              | COMP (Code m o) (Code i m)
              | I i | O o
              | FIX (Code (Sum i o) o)

--data Interprt (c :: Code i o) (r :: i -> *) (j :: o) where
data Interprt :: Code i o -> (i -> *) -> o -> * where
  I_U :: Interprt UNIT r o
  I_L :: Interprt a r o -> Interprt (SUM a b) r o
  I_R :: Interprt b r o -> Interprt (SUM a b) r o
  I_P :: Interprt a r o -> Interprt b r o -> Interprt (PROD a b) r o
  I_I :: r i -> Interprt (I i) r o
  I_O :: Interprt (O o) r o
  I_F :: Fix c r o -> Interprt (FIX c) r o

--data Fix (c :: Code (Sum i o) o) (r :: i -> *) (j :: o) where
data Fix :: Code (Sum i o) o -> (i -> *) -> o -> * where
  Mu :: Interprt c (Sum1 r (Fix c r)) o -> Fix c r o

-- Type-checks in HEAD with either Mu or I_F uncommented, but not with both
