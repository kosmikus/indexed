{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module Pair where

open import Prelude
open import IxFun


----------------------------------------------------------------------
-- Pairs
----------------------------------------------------------------------

-- Code for functor (2 parameters, 1 unused recursive position)
`PairF' : ((⊤ + ⊤) + ⊤) ▸ ⊤
`PairF' = I (inl (inl tt)) ⊗ I (inl (inr tt))

-- Code for fixed point
`Pair' : (⊤ + ⊤) ▸ ⊤
`Pair' = Fix `PairF'

-- Conversions
fromPair′ : {r : Indexed (⊤ + ⊤)} {o : ⊤} 
          → (r (inl o) × r (inr o)) → ⟦ `Pair' ⟧ r o
fromPair′ {o = tt} (x , y) = ⟨ x , y ⟩

fromPair : ∀ {A B} → A × B → ⟦ `Pair' ⟧ (T A ∣ T B) tt
fromPair = fromPair′

toPair′ : {r : Indexed (⊤ + ⊤)} {o : ⊤} 
        → ⟦ `Pair' ⟧ r o → (r (inl o) × r (inr o))
toPair′ {o = tt} ⟨ x , y ⟩ = (x , y)

toPair : ∀ {A B} → ⟦ `Pair' ⟧ (T A ∣ T B) tt → A × B
toPair = toPair′

postulate isoPair₁ : {r : Indexed (⊤ + ⊤)} {o : ⊤} {x : r (inl o) × r (inr o)}
                   → toPair′ {r} (fromPair′ x) ≡ x
postulate isoPair₂ : {r : Indexed (⊤ + ⊤)} {o : ⊤} {x : ⟦ `Pair' ⟧ r o}
                   → fromPair′ {r} (toPair′ x) ≡ x

epPair : (r : Indexed (⊤ + ⊤)) (o : ⊤) → r (inl o) × r (inr o) ≃ ⟦ `Pair' ⟧ r o
epPair r tt = record { from = fromPair′ 
                     ; to   = toPair′
                     ; iso₁ = isoPair₁ {r} ; iso₂ = isoPair₂ }

`PairE' : (⊤ + ⊤) ▸ ⊤
`PairE' = Iso `Pair' (λ f t → f (inl t) × f (inr t)) epPair

-- Concrete map
mapPair : ∀ {A B C D} → (A → B) → (C → D) → (A × C) → (B × D)
mapPair f g = map `PairE' (↑ f ∥ ↑ g) tt

test : Nat × Nat
test = mapPair suc (const 0) (0 , 1)
