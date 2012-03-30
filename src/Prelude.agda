{-# OPTIONS --type-in-type #-}

module Prelude where

open import Relation.Binary.PropositionalEquality public
open import Coinduction public
open import Data.Empty public
open import Data.Unit public hiding (setoid ; decSetoid ; preorder)
open import Data.Sum public renaming (map to _▽_)
open import Data.Product public hiding (map) renaming (_,_ to _,,_)
open import Function public

-- Isomorphisms
infix 3 _≃_
record _≃_ (A B : Set) : Set where
  field
    from  : A → B
    to    : B → A
    iso₁  : ∀ {x} → to (from x) ≡ x
    iso₂  : ∀ {x} → from (to x) ≡ x

-- Reverse function arrow
_←_ : Set → Set → Set
B ← A = A → B

≡≃ : ∀ {A B} → A ≡ B → A ≃ B
≡≃ refl = record { from = id; to = id; iso₁ = refl; iso₂ = refl }

-- Propositional equality utilities
≡→ : ∀ {A B} → A ≡ B → A → B
-- ≡→ p = _≃_.from (≡≃ p)
≡→ refl x = x

≡← : ∀ {A B} → A ≡ B → A ← B
--≡← p = _≃_.to   (≡≃ p)
≡← refl x = x

≡₁ : ∀ {A B} → (p : A ≡ B) → ∀ {x} → (≡← p) ((≡→ p) x) ≡ x
≡₁ refl = refl

≡₂ : ∀ {A B} → (p : A ≡ B) → ∀ {x} → (≡→ p) ((≡← p) x) ≡ x
≡₂ refl = refl
