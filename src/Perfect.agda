{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module Perfect where

open import Nat
open import Prelude
open import IxFun
open import SemiEq

-- This is how Ralf H represents them in his Ameland IFIP talk:
--
-- Perfect = Id + Perfect ∘ Pair =
--
-- This seems to be a more suitable representation for using combinators:
--
-- Perfect′ 0       a = ⊥
-- Perfect′ (suc n) a = Perfect n a × Perfect n a
-- Perfect          a = ∃ (λ n → Perfect′ n a)

-- The actual type
data Perfect (A : Set) : {n : Nat} → Set where
  split : {n : Nat} → A → Perfect A {n} × Perfect A {n} → Perfect A {suc n}
  leaf  : Perfect A {0}

p1 : Perfect Nat
p1 = leaf

p2 : Perfect Nat
p2 = split 0 (p1 , p1)

p2' : Perfect Nat
p2' = split 0 (p1 , p1)

p3 : Perfect Nat
p3 = split 2 (p2 , split 1 (p1 , p1))

p4 : Perfect Nat
p4 = split 3 (p3 , split 4 (p2 , p2))

PerfectF : Nat → (⊤ + Nat) ▸ Nat
PerfectF (zero)  = ! zero
PerfectF (suc n) = ! (suc n) ⊗ I (inl tt) ⊗ I (inr n) ⊗ I (inr n)

`PerfectF' : (⊤ + Nat) ▸ Nat
`PerfectF' = Σ {C = `NatE'} PerfectF

`Perfect' : ⊤ ▸ Nat
`Perfect' = Fix `PerfectF'

fromPerfect′ : {r : Indexed ⊤} {n : Nat} → Perfect (r tt) {n} → ⟦ `Perfect' ⟧ r n
fromPerfect′ {n = suc n} (split x (p1 , p2)) = 
  ⟨ some {x = suc n} (refl , (x , (fromPerfect′ p1 , fromPerfect′ p2))) ⟩
fromPerfect′ {n = zero} leaf = ⟨ some {x = zero} refl ⟩

fromPerfect : {A : Set} {n : Nat} → Perfect A {n} → ⟦ `Perfect' ⟧ (T A) n
fromPerfect = fromPerfect′

toPerfect′ : {r : Indexed ⊤} {n : Nat} → ⟦ `Perfect' ⟧ r n → Perfect (r tt) {n}
toPerfect′ ⟨ some {zero}  refl ⟩                     = leaf
toPerfect′ ⟨ some {suc n} (refl , (x , (p1 , p2))) ⟩ =
  split x (toPerfect′ p1 , toPerfect′ p2)

toPerfect : {A : Set} {n : Nat} → ⟦ `Perfect' ⟧ (T A) n → Perfect A {n}
toPerfect = toPerfect′

postulate isoPerfect₁ : {r : Indexed ⊤} {n : Nat} {x : Perfect (r tt) {n}}
                      → toPerfect′ {r} (fromPerfect′ x) ≡ x
postulate isoPerfect₂ : {r : Indexed ⊤} {n : Nat} {x : ⟦ `Perfect' ⟧ r n}
                      → fromPerfect′ {r} (toPerfect′ x) ≡ x

`PerfectE' : ⊤ ▸ Nat
`PerfectE' = Iso `Perfect' (λ f n → Perfect (f tt) {n})
                           (λ r n → record { from = fromPerfect′ 
                                           ; to   = toPerfect′
                                           ; iso₁ = isoPerfect₁ {r} ; iso₂ = isoPerfect₂ })

mapPerfect : ∀ {n A B} → (A → B) → Perfect A {n} → Perfect B {n}
mapPerfect {n} f = map `PerfectE' (↑ f) n

cataPerfect′ : {n : Nat} {A : Set} {R : Nat → Set}
             → R zero 
             → ({m : Nat} → A → R m × R m → R (suc m))
             → Perfect A {n} → R n
cataPerfect′ {n} {A} {R} r f p = cata `PerfectF' g n (fromPerfect p)
  where
    g : (i : Nat) → ∃ (λ i′ → ⟦ PerfectF i′ ⟧ (T A ∣ R) i) → R i
    g .0       (some {zero}  refl)                     = r
    g .(suc n) (some {suc n} (refl , (x , (p1 , p2)))) = f x (p1 , p2)

cataPerfect : ∀ {n A R} → R → (A → R × R → R) → Perfect A {n} → R
cataPerfect {R = R} r f p = cataPerfect′ {R = const R} r f p

test : Perfect Nat {2}
test = cataPerfect′ leaf (λ {n} a p → split {n = n} a (swap p)) p3

deqPerfectNat : {n : Nat} (x y : Perfect Nat {n}) → Maybe (x ≡ y)
deqPerfectNat = deqt `PerfectE' (const deqNat) _

data Perfect′ (A : Set) : Set where
  split : Perfect′ (A × A) → Perfect′ A
  leaf  : Perfect′ A
