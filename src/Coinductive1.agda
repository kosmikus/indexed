-- Thanks to Nils Anders Danielsson

{-# OPTIONS --guardedness-preserving-type-constructors #-}

module Coinductive1 where

open import Coinduction
open import Data.Empty
open import Data.Nat hiding (fold)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality

mutual

  infixr 2 _⊗_
  infixr 1 _⊕_

  data Code : Set₁ where
    z u     : Code
    k       : (A : Set) → Code
    r       : (c : ∞ Code) → Code
    _⊕_ _⊗_ : (c₁ c₂ : Code) → Code

  ⟦_⟧ : Code → Set
  ⟦ z ⟧       = ⊥
  ⟦ u ⟧       = ⊤
  ⟦ k A ⟧     = A
  ⟦ r c ⟧     = Rec (♯ ⟦ ♭ c ⟧)
  ⟦ c₁ ⊕ c₂ ⟧ = ⟦ c₁ ⟧ ⊎ ⟦ c₂ ⟧
  ⟦ c₁ ⊗ c₂ ⟧ = Σ ⟦ c₁ ⟧ λ _ → ⟦ c₂ ⟧

size : (c : Code) → ⟦ c ⟧ → ℕ
size z         ()
size u         tt       = 0
size (k A)     x        = 0
size (r c)     (fold x) = 1 + size (♭ c) x
size (c₁ ⊕ c₂) (inj₁ x) = size c₁ x
size (c₁ ⊕ c₂) (inj₂ y) = size c₂ y
size (c₁ ⊗ c₂) (x , y)  = size c₁ x + size c₂ y

list : Code → Code
list a = u ⊕ a ⊗ r (♯ list a)

private

  xs : ⟦ list (k ℕ) ⟧
  xs = inj₂ (4 , fold (inj₂ (2 , fold (inj₁ tt))))

  ok : size (list (k ℕ)) xs  ≡ 2
  ok = refl
