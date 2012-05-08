{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Data.Nat where

import Universe

-- Peano style natural numbers
data Peano = Zero | Suc Peano

type NatF = (SUM UNIT (I (R TT)) :: Code (Sum Bot Top) Top)
type Nat = (FIX NatF :: Code Bot Top)

fromNat :: Peano -> Interprt Nat r o
fromNat Zero    = I_F (I_L I_U)
fromNat (Suc n) = I_F (I_R (I_I (RR (fromNat n))))

toNat :: Interprt Nat r o -> Peano
toNat (I_F (I_L I_U))          = Zero
toNat (I_F (I_R (I_I (RR n)))) = Suc (toNat n)
