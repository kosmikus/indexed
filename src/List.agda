{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module List where

open import Prelude
open import IxFun

----------------------------------------------------------------------
-- Lists
----------------------------------------------------------------------

-- Code for the functor (1 parameter, 1 recursive position)
`ListF' : (⊤ + ⊤) ▸ ⊤
`ListF' = U ⊕ (I (inl tt) ⊗ I (inr tt))

-- Code for the fixed point
`List' : ⊤ ▸ ⊤
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

postulate isoList₁ : {r : Indexed ⊤} {o : ⊤} {x : List (r o)}
                   → toList′ {r} (fromList′ x) ≡ x
postulate isoList₂ : {r : Indexed ⊤} {o : ⊤} {x : ⟦ `List' ⟧ r o}
                   → fromList′ {r} (toList′ x) ≡ x

epList : {r : Indexed ⊤} {o : ⊤} → List (r o) ≃ ⟦ `List' ⟧ r o
epList {r} = record { from = fromList′ 
                    ; to   = toList′
                    ; iso₁ = isoList₁ {r} ; iso₂ = isoList₂ }

`ListE' : ⊤ ▸ ⊤
`ListE' = Iso `List' (λ f t → List (f t)) (λ r o → epList)

-- Concrete map
mapList : ∀ {A B} → (A → B) → List A → List B
mapList f = map `ListE' (↑ f) tt

-- Catamorphism               
^ : {F : Indexed ⊤} → F tt → (i : ⊤) → F i
^ x tt = x

foldr : {A R : Set} → (A → R → R) → R → List A → R
foldr {R = R} c n xs = cata {s = T R} `ListF' (^ (const n ▿ uncurry c)) tt (fromList xs)

-- Example use
length : ∀ {A} → List A → Nat
length = foldr (const suc) zero
