{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module Nat where

open import Prelude
open import IxFun
open import SemiEq

----------------------------------------------------------------------
-- Natural numbers
----------------------------------------------------------------------

-- Code for the functor (0 parameters, 1 recursive position)
`NatF' : (⊥ + ⊤) ▸ ⊤
`NatF' = U ⊕ I (inr tt)

-- Code for the fixed point
`Nat' : ⊥ ▸ ⊤
`Nat' = Fix `NatF'

-- Actual type is in Prelude

-- Conversions
fromNat : {r : Indexed ⊥} {o : ⊤} → Nat → ⟦ `Nat' ⟧ r o
fromNat zero    = ⟨ inl tt ⟩
fromNat (suc n) = ⟨ inr (fromNat n) ⟩

toNat : {r : Indexed ⊥} {o : ⊤} → ⟦ `Nat' ⟧ r o → Nat
toNat ⟨ inl tt ⟩ = zero
toNat ⟨ inr n ⟩  = suc (toNat n)

-- Proofs of isomorphism
toFromNat≃ : ∀ {r o} {n : Nat} → toNat {r} {o} (fromNat n) ≡ n
toFromNat≃ {n = zero}  = refl
toFromNat≃ {n = suc _} = cong≡ suc toFromNat≃

fromToNat≃ : ∀ {r o} {x : ⟦ `Nat' ⟧ r o} → (fromNat (toNat x)) ≡ x
fromToNat≃ {x = ⟨ inl tt ⟩} = refl
fromToNat≃ {x = ⟨ inr _  ⟩} = cong≡ (⟨_⟩ ∘ inr) fromToNat≃

`NatE' : ⊥ ▸ ⊤
`NatE' = Iso `Nat' (λ _ _ → Nat) (λ r o → record { from = fromNat 
                                                 ; to   = toNat
                                                 ; iso₁ = toFromNat≃
                                                 ; iso₂ = fromToNat≃ })

-- Catamorphism
cataNat : ∀ {R} → R → (R → R) → Nat → R
cataNat z s n = cata {r = λ ()} `NatF' (λ i → const z ▿ s) tt (fromNat n)

-- Equality
deqNat : (m n : Nat) → Maybe (m ≡ n)
deqNat m n = deqt {r = (λ ())} `NatE' (λ ()) tt m n

-- Example use
addNat : Nat → Nat → Nat
addNat m = cataNat m suc
