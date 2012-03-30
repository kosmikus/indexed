{-# OPTIONS --no-termination-check #-}

module SemiEq where

open import Prelude
open import IxFun


-- Semi-decidable equality
_⇒_ : ∀ {I} → Indexed I → Indexed I → Set
r ⇒ s = ∀ i → (x y : r i) → Maybe (x ≡ y)

infixr 5 _∦_
_∦_ : {I J : Set} {r : Indexed I} {s : Indexed J}
    → (r ⇒ r) → (s ⇒ s) → (r ∣ s) ⇒ (r ∣ s)
(f ∦ g) (inl x) = f x
(f ∦ g) (inr y) = g y

deqt : {I O : Set} {r : Indexed I} (C : I ▸ O)
    → (r ⇒ r) → (⟦ C ⟧ r ⇒ ⟦ C ⟧ r)
deqt Z f o () y
deqt U f o tt tt = just refl
deqt (I i) f o x y = f i x y
deqt (F ↗ g ↘ h) f o x y = deqt F (f ∘ g) (h o) x y
deqt (F ⊕ G) f o (inl x) (inl y) = mapMaybe (cong≡ inl) (deqt F f o x y)
deqt (F ⊕ G) f o (inl x) (inr y) = nothing
deqt (F ⊕ G) f o (inr x) (inl y) = nothing
deqt (F ⊕ G) f o (inr x) (inr y) = mapMaybe (cong≡ inr) (deqt G f o x y)
deqt (F ⊗ G) f o (x1 , x2) (y1 , y2) =       deqt F f o x1 y1 >>= 
                                      λ l → deqt G f o x2 y2 >>= 
                                      λ r → just (cong≡₂ _,_ l r)
deqt (F ⊚ G) f o x y = deqt F (deqt G f) o x y 
deqt (! o) f .o refl refl = just refl
deqt (Σ {C = C} g) f o (some {i1} x) (some {i2} y) with deqt {r = λ _ → _} C (λ ()) tt i1 i2
deqt (Σ g) f o (some x0) (some y) | nothing = nothing
deqt (Σ g) f o (some {i} x0) (some y') | just refl = mapMaybe (cong≡ some) (deqt (g i) f o x0 y')
deqt (Fix F) f o ⟨ x ⟩ ⟨ y ⟩ = mapMaybe (cong≡ ⟨_⟩) (deqt F (f ∦ deqt (Fix F) f) o x y)
deqt {r = r} (Iso C D e) f o x y with e r o

deqt (Iso C D e) f o x y | ep with _≃_.iso₁ ep {x} | _≃_.iso₁ ep {y} | deqt C f o (_≃_.from ep x) (_≃_.from ep y)
deqt (Iso C D e) f o x y | ep | p₁ | p₂ | just p = just (trans≡ (sym≡ p₁) (trans≡ (cong≡ (_≃_.to ep) p) p₂))
deqt (Iso C D e) f o x y | ep | p₁ | p₂ | nothing = nothing
