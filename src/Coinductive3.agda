-- Thanks to Nils Anders Danielsson

{-# OPTIONS --guardedness-preserving-type-constructors #-}

module Coinductive3 where

open import Coinduction
open import Data.Empty
open import Data.Nat hiding (fold)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality


data Kind : Set where
   ind coind : Kind

infixr 2 _⊗_
infixr 1 _⊕_

data Code : Kind → Set₁ where
  z u     : ∀ {k} → Code k
  k       : ∀ {k} (A : Set) → Code k
  r       : ∀ {k} (c : ∞ (Code k)) → Code k
  _⊕_ _⊗_ : ∀ {k} (c₁ c₂ : Code k) → Code k
  inf     : (c : Code coind) → Code coind

⟦_⟧ : ∀ {k} → Code k → Set
⟦ z ⟧       = ⊥
⟦ u ⟧       = ⊤
⟦ k A ⟧     = A
⟦ r c ⟧     = Rec (♯ ⟦ ♭ c ⟧)
⟦ c₁ ⊕ c₂ ⟧ = ⟦ c₁ ⟧ ⊎ ⟦ c₂ ⟧
⟦ c₁ ⊗ c₂ ⟧ = Σ ⟦ c₁ ⟧ λ _ → ⟦ c₂ ⟧
⟦ inf c ⟧   = ∞ ⟦ c ⟧

size : (c : Code ind) → ⟦ c ⟧ → ℕ
size z         ()
size u         tt       = 0
size (k A)     x        = 0
size (r c)     (fold x) = 1 + size (♭ c) x
size (c₁ ⊕ c₂) (inj₁ x) = size c₁ x
size (c₁ ⊕ c₂) (inj₂ y) = size c₂ y
size (c₁ ⊗ c₂) (x , y)  = size c₁ x + size c₂ y
