{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module Pair where

open import Prelude
open import IxFun


----------------------------------------------------------------------
-- Pairs
----------------------------------------------------------------------

-- Code for functor (2 parameters, 1 unused recursive position)
`PairF' : Code ((⊤ + ⊤) + ⊤) ⊤
`PairF' = I (inl (inl tt)) ⊗ I (inl (inr tt))

-- Code for fixed point
`Pair' : Code (⊤ + ⊤) ⊤
`Pair' = Fix `PairF'

-- Conversions
fromPair′ : {r : Indexed (⊤ + ⊤)} {o : ⊤} 
          → (r (inl o) × r (inr o)) → ⟦ `Pair' ⟧ r o
fromPair′ {o = tt} (x , y) = ⟨ x , y ⟩

fromPair : ∀ {A B} → A × B → ⟦ `Pair' ⟧ (T A ∣ T B) tt
fromPair = fromPair′

toPair′ : {r : Indexed (⊤ + ⊤)} {o : ⊤} 
        → ⟦ `Pair' ⟧ r o → T (r (inl o) × r (inr o)) o
toPair′ {o = tt} ⟨ x , y ⟩ = (x , y)

toPair : ∀ {A B} → ⟦ `Pair' ⟧ (T A ∣ T B) tt → A × B
toPair = toPair′

epPair : (r : Indexed (⊤ + ⊤)) (o : ⊤) → r (inl o) × r (inr o) ≃ ⟦ `Pair' ⟧ r o
epPair r tt = record { from = fromPair′ 
                     ; to   = toPair′
                     ; iso₁ = nothing ; iso₂ = nothing }

`PairE' : Code (⊤ + ⊤) ⊤
`PairE' = EP `Pair' (λ f t → f (inl t) × f (inr t)) epPair

-- Concrete map
mapPair : ∀ {A B C D} → (A → B) → (C → D) → (A × C) → (B × D)
mapPair f g = map `PairE' (↑ f ∥ ↑ g) tt

test : Nat × Nat
test = mapPair suc (const 0) (0 , 1)
