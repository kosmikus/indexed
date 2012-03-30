-- {-# OPTIONS --type-in-type #-}

module TestIndexed2CoinductiveNoK where

open import Prelude
open import Indexed
open import Indexed2CoinductiveNoK
open import Data.Nat
import CoinductiveNoK as Coinductive


aSimpleList : μ' ListC (Coinductive.⟦_⟧ Coinductive.U)
aSimpleList = cons Coinductive.tt (cons Coinductive.tt nil)

testList : μ' ListC (Coinductive.⟦_⟧ Coinductive.U) → ℕ
testList l = Coinductive.size _ (from' (Fix ListC) _ (const (Coinductive.U)) (λ _ → refl) _ l)

t₁ : testList aSimpleList ≡ 3
t₁ = refl

{-
testTreeList : μ' TreeListC ℕ → ℕ
testTreeList t = Coinductive.size _ (from' (Fix TreeListC) _ _ t)


t : μ' TreeListC ℕ
t = ⟨ inj₂ (⟨ inj₁ (cons 0 nil) ⟩ , ⟨ inj₁ (cons 1 nil) ⟩) ⟩

t₂ : testTreeList t ≡ 3
t₂ = refl
-}