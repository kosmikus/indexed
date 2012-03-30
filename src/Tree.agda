{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module Tree where

open import Prelude
open import IxFun
open import Nat


----------------------------------------------------------------------
-- Binary trees of naturals
----------------------------------------------------------------------

-- Code for functor (1 parameter, 1 recursive position)
`TreeF' : Code (⊤ + ⊤) ⊤
`TreeF' = I (inl tt) ⊕ I (inr tt) ⊗ I (inr tt)

-- Code for fixed point
`Tree' : Code ⊤ ⊤
`Tree' = Fix `TreeF'

-- Actual datatype
data Tree (A : Set) : Set where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

tree1 : Tree Nat
tree1 = node (leaf 0) (leaf 1)

tree2 : Tree Nat
tree2 = node (node (leaf 2) (leaf 3)) tree1

-- Conversions
fromTree′ : {r : Indexed ⊤} {o : ⊤} → Tree (r o) → ⟦ `Tree' ⟧ r o
fromTree′ {o = tt} (leaf x)   = ⟨ inl x ⟩
fromTree′ {o = tt} (node x y) = ⟨ inr (fromTree′ x , fromTree′ y) ⟩

fromTree : ∀ {A} → Tree A → ⟦ `Tree' ⟧ (T A) tt
fromTree = fromTree′

toTree′ : {r : Indexed ⊤} {o : ⊤} → ⟦ `Tree' ⟧ r o → Tree (r o)
toTree′ {o = tt} ⟨ inl x ⟩       = leaf x
toTree′ {o = tt} ⟨ inr (x , y) ⟩ = node (toTree′ x) (toTree′ y)

toTree : ∀ {A} → ⟦ `Tree' ⟧ (T A) tt → Tree A
toTree = toTree′

epTree : (r : Indexed ⊤) (o : ⊤) → Tree (r o) ≃ ⟦ `Tree' ⟧ r o
epTree r tt = record { from = fromTree′
                     ; to   = toTree′
                     ; iso₁ = nothing ; iso₂ = nothing }

`TreeE' : Code ⊤ ⊤
`TreeE' = EP `Tree' (λ f t → Tree (f t)) epTree

-- Concrete map
mapTree : ∀ {A B} → (A → B) → Tree A → Tree B
mapTree f = map `TreeE' (↑ f) tt

-- Catamorphism
cataTree : {r : Indexed ⊤} {R : Set}
         → ((r tt) → R) → (R → R → R) 
         → Tree (r tt) → R
cataTree {r} n c = cata {r = r} `TreeF' (λ i → n ▿ uncurry c) tt ∘ fromTree′

-- Test
test : Tree Nat
test = mapTree suc tree2