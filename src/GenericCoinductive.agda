{-# OPTIONS --no-positivity-check #-}

module GenericCoinductive where

-- Demonstrates how an encoding that
-- actually involves recursion can be
-- expressed in Agda.

open import Coinduction
open import Data.Unit
open import Data.Nat
open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

-- Isomorphisms
infix 3 _≃_
record _≃_ (A : Set) (B : Set₁) : Set₁ where
  field
    from  : A → B
    to    : B → A
    iso₁  : ∀ {x} → to (from x) ≡ x
    iso₂  : ∀ {x} → from (to x) ≡ x

-- Codes and their interpretation
mutual
  data Code : Set₁ where
    unit : Code
    nat  : Code
    _⊕_  : ∞ Code → ∞ Code → Code
    _⊗_  : ∞ Code → ∞ Code → Code
    iso  : (A : Set) → (C : ∞ Code) → A ≃ ⟦ ♭ C ⟧ → Code

  -- Going for a one-datatype interpretation. This is the
  -- easiest way I know to enforce that we're interested in
  -- an *inductive* interpretation over a *coinductive* code.
  data ⟦_⟧ : Code → Set₁ where
    tt  : ⟦ unit ⟧
    nr  : ℕ → ⟦ nat ⟧
    inl : {C D : ∞ Code} → ⟦ ♭ C ⟧ → ⟦ C ⊕ D ⟧
    inr : {C D : ∞ Code} → ⟦ ♭ D ⟧ → ⟦ C ⊕ D ⟧
    _,_ : {C D : ∞ Code} → ⟦ ♭ C ⟧ → ⟦ ♭ D ⟧ → ⟦ C ⊗ D ⟧
    emb : {A : Set} → {C : ∞ Code} → {i : A ≃ ⟦ ♭ C ⟧} → (a : A) → ⟦ iso A C i ⟧
