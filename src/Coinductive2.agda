-- Thanks to Nils Anders Danielsson

{-# OPTIONS --guardedness-preserving-type-constructors #-}

module Coinductive2 where

open import Coinduction
open import Data.Empty
open import Data.Nat hiding (fold)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Bool
open import Relation.Binary.PropositionalEquality


infixr 2 _⊗_
infixr 1 _⊕_

data Code : Set₁ where
  z u     : Code
  k       : (A : Set) → Code
  r       : (c : ∞ Code) → Code
  _⊕_ _⊗_ : (c₁ c₂ : Code) → Code
  inf     : (c : Code) → Code

⟦_⟧ : Code → Set
⟦ z ⟧       = ⊥
⟦ u ⟧       = ⊤
⟦ k A ⟧     = A
⟦ r c ⟧     = Rec (♯ ⟦ ♭ c ⟧)
⟦ c₁ ⊕ c₂ ⟧ = ⟦ c₁ ⟧ ⊎ ⟦ c₂ ⟧
⟦ c₁ ⊗ c₂ ⟧ = Σ ⟦ c₁ ⟧ λ _ → ⟦ c₂ ⟧
⟦ inf c ⟧   = ∞ ⟦ c ⟧

stream : Code → Code
stream a = a ⊗ inf (r (♯ stream a))

private

  zeros : ⟦ stream (k ℕ) ⟧
  zeros = 0 , ♯ fold zeros
