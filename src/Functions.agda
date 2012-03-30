{-# OPTIONS --no-termination-check #-}

module Functions where

-- Demonstrates how an encoding that
-- actually involves recursion can be
-- expressed in Agda.

open import GenericCoinductive
open import Data.Nat
open import Coinduction

-- Sample generic function that sums up all natural numbers in a type
sum : (A : Code) → ⟦ A ⟧ → ℕ
sum unit    x       = 0
sum nat     (nr n)  = n
sum (A ⊕ B) (inl x) = sum (♭ A) x
sum (A ⊕ B) (inr x) = sum (♭ B) x
sum (A ⊗ B) (x , y) = sum (♭ A) x + sum (♭ B) y
sum (iso A C i) (emb a) = sum (♭ C) (_≃_.from i a)

-- Sample generic producer. This doesn't termination-check (and
-- rightly so, because we might descend an infinite path in the
-- code here, and thereby produce an infinite structure).
empty : (A : Code) → ⟦ A ⟧
empty unit    = tt
empty nat     = nr 0
empty (A ⊕ B) = inl (empty (♭ A))
empty (A ⊗ B) = empty (♭ A) , empty (♭ B)
empty (iso A C i) = emb (_≃_.to i (empty (♭ C)))
