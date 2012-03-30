{-# OPTIONS --type-in-type #-}

module TestPolyP2Coinductive where

open import Prelude
open import PolyP
open import PolyP2Coinductive
open import Data.Nat
import Coinductive


testList : μ ListC ℕ → ℕ
testList l = Coinductive.size (p2cC ListC ℕ) (fromμPolyP ListC l)

t₁ : testList aList ≡ 5
t₁ = refl


testTreeList : μ TreeListC ℕ → ℕ
testTreeList t = Coinductive.size (p2cC TreeListC ℕ) (fromμPolyP TreeListC t)


t : μ TreeListC ℕ
t = ⟨ inj₂ (⟨ inj₁ (cons 0 nil) ⟩ , ⟨ inj₁ (cons 1 nil) ⟩) ⟩

t₂ : testTreeList t ≡ 10
t₂ = refl
