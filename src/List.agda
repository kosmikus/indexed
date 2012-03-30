{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module List where

open import Prelude
open import IxFun

----------------------------------------------------------------------
-- Lists
----------------------------------------------------------------------

-- Code for the functor (1 parameter, 1 recursive position)
`ListF' : Code (⊤ + ⊤) ⊤
`ListF' = U ⊕ (I (inl tt) ⊗ I (inr tt))

-- Code for the fixed point
`List' : Code ⊤ ⊤
`List' = Fix `ListF'

-- Actual datatype
infixr 6 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- Conversions
fromList′ : {r : Indexed ⊤} {o : ⊤} → List (r o) → ⟦ `List' ⟧ r o
fromList′ {o = tt} []       = ⟨ inl tt ⟩
fromList′ {o = tt} (x ∷ xs) = ⟨ inr (x , fromList′ xs) ⟩

fromList : ∀ {A} → List A → ⟦ `List' ⟧ (T A) tt
fromList = fromList′

toList′ : {r : Indexed ⊤} {o : ⊤} → ⟦ `List' ⟧ r o → List (r o)
toList′ {o = tt} ⟨ inl tt ⟩       = []
toList′ {o = tt} ⟨ inr (x , xs) ⟩ = x ∷ toList′ xs

toList : ∀ {A} → ⟦ `List' ⟧ (T A) tt → List A
toList = toList′

epList : {r : Indexed ⊤} {o : ⊤} → List (r o) ≃ ⟦ `List' ⟧ r o
epList = record { from = fromList′ 
                ; to   = toList′
                ; iso₁ = nothing ; iso₂ = nothing }

`ListE' : Code ⊤ ⊤
`ListE' = EP `List' (λ f t → List (f t)) (λ r o → epList)

-- Concrete map
mapList : ∀ {A B} → (A → B) → List A → List B
mapList f = map `ListE' (↑ f) tt

-- Catamorphism               
^ : {F : Indexed ⊤} → F tt → (i : ⊤) → F i
^ x tt = x

cataList : {A R : Set} → R → (A → R → R) → List A → R
cataList {R = R} n c xs = cata {s = T R} `ListF' (^ (const n ▿ uncurry c)) tt (fromList xs)

-- Example use
length : ∀ {A} → List A → Nat
length = cataList zero (const suc)
