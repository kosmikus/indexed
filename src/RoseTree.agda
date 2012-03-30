{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module RoseTree where

open import Prelude
open import IxFun
open import List

----------------------------------------------------------------------
-- Rose trees
----------------------------------------------------------------------

-- Code for functor (1 parameter, 1 recursive position)
`RoseF' : Code (⊤ + ⊤) ⊤
`RoseF' = I (inl tt) ⊗ `List' ⊚ I (inr tt)

-- Code for fixed point
`Rose' : Code ⊤ ⊤
`Rose' = Fix `RoseF'

-- Actual datatype
data Rose (A : Set) : Set where
  fork : A → List (Rose A) → Rose A

r1 : Rose Nat
r1 = fork 0 []

r2 : Rose Nat
r2 = fork 5 (fork 4 [] ∷ (fork 3 [] ∷ (fork 2 [] ∷ (fork 1 (r1 ∷ []) ∷ []))))

-- Conversions (note that there are even three variants now)
fromRose′ : {r : Indexed ⊤} {o : ⊤} → Rose (r o) → ⟦ `Rose' ⟧ r o
fromRose′ {o = tt} (fork x xs) = ⟨ x , fromList′ (map `ListE' (↑ fromRose′) tt xs) ⟩
--fromRose′ {o = tt} (fork x xs) = ⟨ x , map `List'  (λ i → fromRose′) tt ((fromList′ xs)) ⟩

fromRose : {A : Set} → Rose A → ⟦ `Rose' ⟧ (T A) tt
fromRose = fromRose′


toRose′ : {r : Indexed ⊤} {o : ⊤} → ⟦ `Rose' ⟧ r o → Rose (r o)
toRose′ {o = tt} ⟨ x , xs ⟩ = fork x (map `ListE' (↑ toRose′) tt (toList′ xs))
--toRose′ {o = tt} ⟨ x , xs ⟩ = fork x (toList′ (map `List' (λ i → toRose′) tt xs))

toRose : {A : Set} → ⟦ `Rose' ⟧ (T A) tt → Rose A
toRose = toRose′

epRose : (r : Indexed ⊤) (o : ⊤) → Rose (r o) ≃ ⟦ `Rose' ⟧ r o
epRose r o = record { from = fromRose′
                    ; to   = toRose′
                    ; iso₁ = nothing ; iso₂ = nothing }

`RoseE' : Code ⊤ ⊤
`RoseE' = EP `Rose' (λ f t → Rose (f t)) epRose

-- Concrete map
mapRose : {A B : Set} → (A → B) → Rose A → Rose B
mapRose f = map `RoseE' (↑ f) tt


-- Catamorphism
cataRose : {A R : Set} → (A → List R → R) → Rose A → R
cataRose {A} {R} f xs = cata {⊤} {⊤} {T A} {T R} `RoseF'
                          g tt (fromRose xs)
  where
    g : ⟦ `RoseF' ⟧ (T A ∣ T R) ⇉ T R
    g tt (x , y) = f x (toList (map `List' h tt y))
      where
        h : (i : ⊤) → R → T R i
        h tt r = r
