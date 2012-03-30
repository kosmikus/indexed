{-# OPTIONS --type-in-type #-}

module TestRegular2Coinductive where

open import Prelude
open import Regular
open import Regular2Coinductive
open import Data.Nat
import Coinductive


test : μ NatC → ℕ
test n = Coinductive.size (r2cC NatC) (fromμRegular NatC n)

t₁ : test aNat ≡ 3
t₁ = refl
