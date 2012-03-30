{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module TestPolyP2Indexed where

open import Prelude
open import PolyP
open import PolyP2Indexed
open import Data.Nat
import Indexed


-- Could certainly be improved, but does the trick for now
test : μ ListC ℕ → ℕ
test l = Indexed.size (p2iC ListC) g (fromμP ListC l) where
  g : (i : ⊤ ⊎ ⊤) → [ (const ℕ) , Indexed.μ (p2iC ListC) (const ℕ) ] i → ℕ
  g (inj₁ tt) x = 1
  g (inj₂ tt) x = Indexed.size (Indexed.Fix (p2iC ListC)) (λ _ _ → 1) x

t₁ : test aList ≡ 3
t₁ = refl
