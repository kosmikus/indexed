{-# OPTIONS --type-in-type #-}

module TestFunctions where

open import Prelude
open import Data.Nat
import Regular     as R
import PolyP       as P
import Indexed     as I
import Coinductive as IG

import Regular2PolyP       as R2P
import PolyP2Indexed       as P2I
import Indexed2Coinductive as I2IG

-- I → IG
test1 : ℕ
test1 = IG.size 
          (I2IG.i2cC' (I.Fix I.ListC) (const ℕ) tt)
          (I2IG.from' (I.Fix I.ListC) _ _ I.aList)

-- P → I → IG
test2 : ℕ
test2 = IG.size 
          (I2IG.i2cC' (I.Fix (P2I.p2iC (P.ListC))) (const ℕ) tt)
          (I2IG.from' (I.Fix (P2I.p2iC (P.ListC))) _         _   (I.⟨_⟩ (P2I.fromμP P.ListC P.aList)))

-- R → P → I → IG
test3 : ℕ
test3 = IG.size 
          (I2IG.i2cC' (I.Fix (P2I.p2iC (R2P.r2pC R.NatC))) (const ⊥) tt)
          (I2IG.from' (I.Fix (P2I.p2iC (R2P.r2pC R.NatC))) _         _   
            (I.⟨_⟩ (P2I.fromμP (R2P.r2pC R.NatC) (R2P.fromμRegular R.NatC R.aNat))))
