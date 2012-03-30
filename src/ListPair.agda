{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module ListPair where

open import Prelude
open import IxFun
open import List
open import Pair


----------------------------------------------------------------------
-- Lists of pairs
----------------------------------------------------------------------

`ListPair' : Code (⊤ + ⊤) ⊤
`ListPair' = `List' ⊚ `Pair'

-- Conversions
fromListPair′ : {r : Indexed (⊤ + ⊤)} {o : ⊤}
              → List ((r (inl tt)) × (r (inr tt))) 
              → ⟦ `ListPair' ⟧ r o
fromListPair′ {o = tt} xs = map `List' (λ i → fromPair′ {o = i}) tt (fromList′ xs)

toListPair′ : {r : Indexed (⊤ + ⊤)} {o : ⊤}
            → ⟦ `ListPair' ⟧ r o
            → List ((r (inl tt)) × (r (inr tt))) 
toListPair′ {o = tt} xs = toList′ (map `List' (λ i → toPair′ {o = i}) tt xs)


-- Concrete map
mapListPair : ∀ {A B C D} → (A → B) → (C → D) → List (A × C) → List (B × D)
mapListPair f g xy = toListPair′ (map `ListPair' (↑ f ∥ ↑ g) tt (fromListPair′ xy))
