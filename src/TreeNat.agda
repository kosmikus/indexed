{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module TreeNat where

open import Prelude
open import IxFun
open import Nat


----------------------------------------------------------------------
-- Binary trees of naturals
----------------------------------------------------------------------

-- Code for functor (0 parameters, 1 recursive position)
`TreeF' : Code (⊥ + ⊤) ⊤
`TreeF' = Y inl `NatE' ⊕ I (inr tt) ⊗ I (inr tt)

-- Code for fixed point
`Tree' : Code ⊥ ⊤
`Tree' = Fix `TreeF'

-- Actual datatype
data Tree : Set where
  leaf : Nat → Tree
  node : Tree → Tree → Tree

tree1 : Tree
tree1 = node (leaf 0) (leaf 1)

tree2 : Tree
tree2 = node (node (leaf 2) (leaf 3)) tree1

-- Conversions
fromTree′ : {r : Indexed ⊥} {o : ⊤} → Tree → ⟦ `Tree' ⟧ r o
fromTree′ {o = tt} (leaf x)   = ⟨ inl x ⟩
fromTree′ {o = tt} (node x y) = ⟨ inr (fromTree′ x , fromTree′ y) ⟩

fromTree : Tree → ⟦ `Tree' ⟧ (λ ()) tt
fromTree = fromTree′

toTree′ : {r : Indexed ⊥} {o : ⊤} → ⟦ `Tree' ⟧ r o → Tree
toTree′ {o = tt} ⟨ inl x ⟩       = leaf x
toTree′ {o = tt} ⟨ inr (x , y) ⟩ = node (toTree′ x) (toTree′ y)

toTree : ⟦ `Tree' ⟧ (λ ()) tt → Tree
toTree = toTree′

epTree : (r : Indexed ⊥) (o : ⊤) → Tree ≃ ⟦ `Tree' ⟧ r o
epTree r tt = ep fromTree′ toTree′

`TreeE' : Code ⊥ ⊤
`TreeE' = EP `Tree' (λ _ _ → Tree) epTree

-- Catamorphism
cataTree : {r : Indexed ⊥} {R : Set}
         → (Nat → R) → (R → R → R) 
         → Tree → R
cataTree {r} n c = cata {r = r} `TreeF' (λ i → (n ▿ uncurry c)) tt ∘ fromTree′

depthTree : Tree → Nat
depthTree = cataTree {r = λ ()} (const 0) (λ m n → suc (maxNat m n)) where
  maxNat : Nat → Nat → Nat
  maxNat zero    n       = n
  maxNat m       zero    = m
  maxNat (suc m) (suc n) = suc (maxNat m n)

-- Test
test : Nat
test = depthTree tree2
