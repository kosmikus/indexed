
module CoinductiveNoK where

open import Coinduction
open import Prelude
open import Data.Nat


-- Codes and their interpretation
mutual
  data Code : Set where
    Z    : Code
    U    : Code
    R    : ∞ Code → Code
    _⊕_  : Code → Code → Code
    _⊗_  : Code → Code → Code

  -- Going for a one-datatype interpretation. This is the
  -- easiest way I know to enforce that we're interested in
  -- an *inductive* interpretation over a *coinductive* code.
  data ⟦_⟧ : Code → Set where
    tt  : ⟦ U ⟧
    rec : {C : ∞ Code} → ⟦ ♭ C ⟧ → ⟦ R C ⟧
    inl : {C D : Code} → ⟦ C ⟧ → ⟦ C ⊕ D ⟧
    inr : {C D : Code} → ⟦ D ⟧ → ⟦ C ⊕ D ⟧
    _,_ : {C D : Code} → ⟦ C ⟧ → ⟦ D ⟧ → ⟦ C ⊗ D ⟧


-- Sample generic function that computes the size of a term
size : (A : Code) → ⟦ A ⟧ → ℕ
size Z         ()
size U            x  = 1
size (R C)   (rec x) = 1 + size (♭ C) x
size (A ⊕ B) (inl x) = size A x
size (A ⊕ B) (inr x) = size B x
size (A ⊗ B) (x , y) = size A x + size B y
