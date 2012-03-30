{-# OPTIONS --no-positivity-check #-}

module Datatypes where

open import GenericCoinductive
open import Functions
open import Data.Nat
open import Coinduction
open import Relation.Binary.PropositionalEquality


-- Example: natural numbers
natI : ℕ ≃ ⟦ nat ⟧
natI = record { from = nr; to = toNat; iso₁ = refl; iso₂ = isoNat₂} where
  toNat : ⟦ nat ⟧ → ℕ
  toNat (nr n) = n
  isoNat₂ : {n : ⟦ nat ⟧} → nr (toNat n) ≡ n
  isoNat₂ {nr _} = refl

natC : Code
natC = iso ℕ (♯ nat) natI


-- Example: lists
open import Data.List hiding (sum)

listC : ∞ Code → Code
listC A = ♯ unit ⊕ ♯ (A ⊗ ♯ listC A)

list : (A : Set) → (C : ∞ Code) → (A ≃ ⟦ ♭ C ⟧) → Code
list A C i = iso (List A) (♯ (listC C)) listIso where
  fromList : List A → ⟦ listC C ⟧
  fromList []       = inl tt
  fromList (x ∷ xs) = inr (_≃_.from i x , fromList xs)

  toList : ⟦ listC C ⟧ → List A
  toList (inl tt)       = []
  toList (inr (x , xs)) = _≃_.to i x ∷ toList xs

  isoList₁ : {x : List A} → toList (fromList x) ≡ x
  isoList₁ {[]}     = refl
  isoList₁ {x ∷ xs} = cong₂ _∷_ (_≃_.iso₁ i) (isoList₁ {xs})

  isoList₂ : {x : ⟦ listC C ⟧} → fromList (toList x) ≡ x
  isoList₂ {inl tt}       = refl
  isoList₂ {inr (x , xs)} = cong inr (cong₂ _,_ (_≃_.iso₂ i) (isoList₂ {xs}))
  listIso = record { from = fromList; to = toList; iso₁ = isoList₁; iso₂ = isoList₂}

test₁ : sum (list ℕ (♯ nat) natI) (emb (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])) ≡ 10
test₁ = refl

-- Example: trees (without isomorphism for now)
tree : ∞ Code → Code
tree A = A ⊕ ♯ (♯ tree A ⊗ ♯ tree A)

-- constructor functions for trees
leaf : {A : ∞ Code} → ⟦ ♭ A ⟧ → ⟦ tree A ⟧
leaf x = inl x

node : {A : ∞ Code} → ⟦ tree A ⟧ → ⟦ tree A ⟧ → ⟦ tree A ⟧
node x y = inr (x , y)

test₂ : sum (tree (♯ nat)) (node (leaf (nr 5)) (leaf (nr 7))) ≡ 12
test₂ = refl