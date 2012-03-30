{-# OPTIONS --type-in-type #-}

module TestIndexed2CoinductiveAlt where

open import Prelude
open import Indexed
open import Indexed2CoinductiveAlt
open import Data.Nat
import Coinductive


testList : μ' ListC ℕ → ℕ
testList l = Coinductive.size _ (fromIndexed (Fix ListC) _ _ l)

t₁ : testList nil ≡ 2
t₁ = refl
t₂ : testList (cons 0 nil) ≡ 4
t₂ = refl
t₃ : testList (cons 0 (cons 1 nil)) ≡ 6
t₃ = refl

-- This looks better!