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
`RoseF' : (⊤ + ⊤) ▸ ⊤
`RoseF' = I (inl tt) ⊗ `List' ⊚ I (inr tt)

-- Code for fixed point
`Rose' : ⊤ ▸ ⊤
`Rose' = Fix `RoseF'

-- Actual datatype
data Rose (A : Set) : Set where
  fork : A → List (Rose A) → Rose A

r1 : Rose Nat
r1 = fork 0 []

r2 : Rose Nat
r2 = fork 5 (fork 4 [] ∷ (fork 3 [] ∷ (fork 2 [] ∷ (fork 1 (r1 ∷ []) ∷ []))))

-- Conversions
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

postulate isoRose₁ : {r : Indexed ⊤} {o : ⊤} {x : Rose (r o)}
                   → toRose′ {r} (fromRose′ x) ≡ x
postulate isoRose₂ : {r : Indexed ⊤} {o : ⊤} {x : ⟦ `Rose' ⟧ r o}
                   → fromRose′ {r} (toRose′ x) ≡ x

epRose : (r : Indexed ⊤) (o : ⊤) → Rose (r o) ≃ ⟦ `Rose' ⟧ r o
epRose r o = record { from = fromRose′
                    ; to   = toRose′
                    ; iso₁ = isoRose₁ {r} ; iso₂ = isoRose₂ }

`RoseE' : ⊤ ▸ ⊤
`RoseE' = Iso `Rose' (λ f t → Rose (f t)) epRose

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
