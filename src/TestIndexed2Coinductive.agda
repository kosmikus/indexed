{-# OPTIONS --type-in-type #-}

module TestIndexed2Coinductive where

open import Prelude
open import Indexed
open import Indexed2Coinductive
open import Data.Nat
import Coinductive


testList : μ' ListC ℕ → ℕ
testList l = Coinductive.size _ (from' (Fix ListC) _ _ l)

t₁ : testList nil ≡ 2
t₁ = refl
t₂ : testList (cons 0 nil) ≡ 3
t₂ = refl
t₃ : testList (cons 0 (cons 1 nil)) ≡ 3
t₃ = refl


testTreeList : μ' TreeListC ℕ → ℕ
testTreeList t = Coinductive.size _ (from' (Fix TreeListC) _ _ t)


t : μ' TreeListC ℕ
t = ⟨ inj₂ (⟨ inj₁ (cons 0 nil) ⟩ , ⟨ inj₁ (cons 1 nil) ⟩) ⟩

t₄ : testTreeList t ≡ 3
t₄ = refl

-- These results are clearly not what we want!