{-# OPTIONS --universe-polymorphism #-}

module Coinductive where

open import Coinduction
open import Prelude
open import Data.Nat hiding (suc)
open import Level


-- Codes and their interpretation
mutual
  data Code {ℓ : Level} : Set (suc ℓ) where
    Z    : Code
    U    : Code
    K    : Set ℓ → Code
    R    : ∞ Code → Code
    _⊕_  : Code → Code → Code
    _⊗_  : Code → Code → Code

  -- Going for a one-datatype interpretation. This is the
  -- easiest way I know to enforce that we're interested in
  -- an *inductive* interpretation over a *coinductive* code.
  data ⟦_⟧ {ℓ : Level} : Code → Set (suc ℓ) where
    tt  : ⟦ U ⟧
    k   : {A : Set ℓ} → A → ⟦ K A ⟧
    rec : {C : ∞ Code} → ⟦ ♭ C ⟧ → ⟦ R C ⟧
    inl : {C D : Code} → ⟦ C ⟧ → ⟦ C ⊕ D ⟧
    inr : {C D : Code} → ⟦ D ⟧ → ⟦ C ⊕ D ⟧
    _,_ : {C D : Code} → ⟦ C ⟧ → ⟦ D ⟧ → ⟦ C ⊗ D ⟧

unk : {ℓ : Level} {A : Set ℓ} → ⟦ K A ⟧ → A
unk (k a) = a

-- Sample generic function that computes the size of a term
size : {ℓ : Level} (A : Code {ℓ}) → ⟦ A ⟧ → ℕ
size Z         ()
size U            x  = 1
size (K X)     (k x) = 1
size (R C)   (rec x) = 1 + size (♭ C) x
size (A ⊕ B) (inl x) = size A x
size (A ⊕ B) (inr x) = size B x
size (A ⊗ B) (x , y) = size A x + size B y
