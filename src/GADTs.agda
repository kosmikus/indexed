{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module GADTs where

open import Prelude
open import IxFun
open import Nat

----------------------------------------------------------------------
-- Vectors (unsurprisingly similar to Perfect trees)
----------------------------------------------------------------------

-- Code for the functor (1 parameter, n recursive positions)
VecF : Nat → Code (⊤ + Nat) Nat
VecF zero    = ! 0
VecF (suc n) = ! (suc n) ⊗ I (inl tt) ⊗ I (inr n)

`VecF' : Code (⊤ + Nat) Nat
`VecF' = Σ {r = λ ()} {o = tt} {C = `NatE'} VecF

-- Code for the fixed point
`Vec' : Code ⊤ Nat
`Vec' = Fix `VecF'

-- Actual type
infixr 5 _∷_

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

-- Conversions
fromVec′ : {r : Indexed ⊤} {n : Nat} → Vec (r tt) n → ⟦ `Vec' ⟧ r n
fromVec′ {r} {0}     []      = ⟨ (some {_} {_} {0}     refl) ⟩
fromVec′ {r} {suc n} (h ∷ t) = ⟨ (some {_} {_} {suc n} (refl , (h , fromVec′ t))) ⟩
fromVec : {A : Set} {n : Nat} → Vec A n → ⟦ `Vec' ⟧ (T A) n
fromVec = fromVec′

toVec′ : {r : Indexed ⊤} {n : Nat} → ⟦ `Vec' ⟧ r n → Vec (r tt) n
toVec′ ⟨ some {zero}  refl             ⟩ = []
toVec′ ⟨ some {suc n} (refl , (h , t)) ⟩ = h ∷ toVec′ t

toVec : {A : Set} {n : Nat} → ⟦ `Vec' ⟧ (T A) n → Vec A n
toVec = toVec′

`VecE' : Code ⊤ Nat
`VecE' = EP `Vec' (λ f → Vec (f tt)) (λ r t → ep fromVec′ toVec′)

-- Map
mapVec : ∀ {n A B} → (A → B) → Vec A n → Vec B n
mapVec {n} f = map `VecE' (↑ f) n

-- Catamorphism
cataVec′ : {n : Nat} {A : Set} {R : Nat → Set}
         → R zero 
         → ({m : Nat} → A → R m → R (suc m))
         → Vec A n → R n
cataVec′ {n} {A} {R} nil cons = cata `VecF' g n ∘ fromVec
  where
    g : (i : Nat) → ∃ (λ i′ → ⟦ VecF i′ ⟧ (T A ∣ R) i) → R i
    g .0       (some {zero}  refl)             = nil
    g .(suc n) (some {suc n} (refl , (h , t))) = cons h t

cataVec : ∀ {n A R} → R → (A → R → R) → Vec A n → R
cataVec {R = R} nil cons = cataVec′ {R = const R} nil cons

