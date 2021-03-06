{-# OPTIONS --no-termination-check #-}

module Eq where

open import Prelude
open import IxFun


_⇒_ : ∀ {I} → Indexed I → Indexed I → Set
r ⇒ s = ∀ i → (x y : r i) → (x d≡ y)

infixr 5 _∦_
_∦_ : {I J : Set} {r : Indexed I} {s : Indexed J}
    → (r ⇒ r) → (s ⇒ s) → (r ∣ s) ⇒ (r ∣ s)
(f ∦ g) (inl x) = f x
(f ∦ g) (inr y) = g y


-- Decidable homogeneous equality (terribly ugly for now)
inlCong : {A B : Set} {x y : A} → (inl {_} {A} {B} x ≡ inl y) → (x ≡ y)
inlCong refl = refl

inrCong : {A B : Set} {x y : B} → (inr {_} {A} {B} x ≡ inr y) → (x ≡ y)
inrCong refl = refl

,Cong : {A B : Set} {x1 y1 : A} {x2 y2 : B} 
      → ((x1 , x2) ≡ (y1 , y2)) → ((x1 ≡ y1) × (x2 ≡ y2))
,Cong refl = refl , refl

--data ∃ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (B : A → Set ℓ₂) : Set (max ℓ₁ ℓ₂) where
--  some : {x : A} → B x → ∃ B

ex∃ : {A : Set} {B : A → Set} → ∃ {A = A} B → A
ex∃ (some {x = i} _) = i

someCong : {A : Set} {B : Indexed A} {i : A} {x y : B i}
         → ((some {B = B} x) ≡ (some y)) → (x ≡ y)
someCong refl = refl


Dep≡ : {A : Set} {B : A → Set} {i j : A} → (i ≡ j) → B i → B j → Set
Dep≡ refl x y = x ≡ y

someCong′ : {A : Set} {B : A → Set}
            {i j : A} {x : B i} {y : B j}
          → ((some {B = B} {x = i} x) ≡ (some {x = j} y)) → ∃ {A = i ≡ j} (λ p → Dep≡ {A} {B} p x y)
someCong′ {A} {B} {i} {.i} {x} {.x} refl = some {x = refl} refl

--  data μ {I O : Set} (F : Code (I + O) O) (r : Indexed I) (o : O) : Set where
--    ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

⟨⟩Cong : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
         {x y : ⟦ F ⟧ (r ∣ μ F r) o}
       → (⟨_⟩ {I} {O} {F} {r} {o} x ≡ ⟨ y ⟩) → (x ≡ y)
⟨⟩Cong refl = refl

deq : {I O : Set} {r : Indexed I} (C : Code I O)
    → (r ⇒ r) → (⟦ C ⟧ r ⇒ ⟦ C ⟧ r)
deq Z f o () y
deq U f o tt tt = yes refl
deq (I i) f o x y = f i x y
deq (X g F) f o x y = deq F f (g o) x y
deq (Y g F) f o x y = deq F (f ∘ g) o x y

deq (F ⊕ G) f o (inl x) (inl y) with deq F f o x y
deq (F ⊕ G) f o (inl x) (inl .x) | yes refl = yes refl
...                              | no  ¬p   = no (¬p ∘ inlCong)
deq (F ⊕ G) f o (inl x) (inr y) = no (λ ())
deq (F ⊕ G) f o (inr x) (inl y) = no (λ ())
deq (F ⊕ G) f o (inr x) (inr y) with deq G f o x y
deq (F ⊕ G) f o (inr x) (inr .x) | yes refl = yes refl
...                              | no  ¬p   = no (¬p ∘ inrCong)

deq (F ⊗ G) f o (x1 , x2) (y1 , y2) with deq F f o x1 y1 | deq G f o x2 y2
deq (F ⊗ G) f o (.y1 , .y2) (y1 , y2) | yes refl | yes refl = yes refl
deq (F ⊗ G) f o (.y1 , x2)  (y1 , y2) | yes refl | no  ¬p   = no (¬p ∘ snd ∘ ,Cong)
deq (F ⊗ G) f o (x1  , x2)  (y1 , y2) | no  ¬p   | _        = no (¬p ∘ fst ∘ ,Cong)

deq (F ⊚ G) f o x y = deq F (deq G f) o x y
deq (! o) f .o refl refl = yes refl
deq (Σ {C = C} g) f o (some {i1} x) (some {i2} y) with deq C (λ ()) tt i1 i2
deq (Σ g) f o (some {i} x) (some y) | yes refl with deq (g i) f o x y
deq (Σ g) f o (some x) (some .x) | yes refl | yes refl = yes refl
deq (Σ g) f o (some x) (some y)  | yes refl | no  ¬p   = no (¬p ∘ someCong)
deq (Σ g) f o (some x) (some y)  | no ¬p               = no (¬p ∘ ex∃ ∘ someCong′)

deq (Fix F) f o ⟨ x ⟩ ⟨ y ⟩ with deq F (f ∦ deq (Fix F) f) o x y
deq (Fix F) f o ⟨ x ⟩ ⟨ .x ⟩ | yes refl = yes refl
deq (Fix F) f o ⟨ x ⟩ ⟨ y ⟩  | no  ¬p   = no (¬p ∘ ⟨⟩Cong)

-- Requires decidable equality on the EP...
deq {r = r} (EP C D e) f o x y with
    _≃_.iso₁ (e r o) {x} 
  | _≃_.iso₁ (e r o) {y}
  | deq C f o (_≃_.from (e r o) x) (_≃_.from (e r o) y)
deq (EP C D e) f o x y | p₁ | p₂ | p = {!!}
