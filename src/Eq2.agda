{-# OPTIONS --no-termination-check #-}

open import Prelude

module Eq2
    -- For IxFun2
    (IxCode : Set)
    (_∔_    : IxCode → IxCode → IxCode)
    (⟪_⟫    : IxCode → Set)
    (∔→+    : {A B : IxCode} → ⟪ A ∔ B ⟫ → ⟪ A ⟫ + ⟪ B ⟫)
    -- For equality
    (≡Ix    : (I J : IxCode) → Maybe (I ≡ J))
  where

import IxFun2
open IxFun2 IxCode _∔_ ⟪_⟫ ∔→+


_⇒_ : ∀ {I} → Indexed I → Indexed I → Set
r ⇒ s = ∀ i → r i → s i → Bool

infixr 5 _∦_
_∦_ : {I J : IxCode} {r s : Indexed I} {u v : Indexed J}
    → (r ⇒ s) → (u ⇒ v) → (r ∣ u) ⇒ (s ∣ v)
(f ∦ g) x with ∔→+ x
(f ∦ g) _ | (inl x) = f x
(f ∦ g) _ | (inr y) = g y


-- heterogeneous equality
-- still problematic with X and Y
eq2 : {I O : IxCode} {r s : Indexed I} (C D : Code I O)
    → ({I : IxCode} → (i j : ⟪ I ⟫) → Maybe (i ≡ j))
    → (r ⇒ s) → ⟦ C ⟧ r ⇒ ⟦ D ⟧ s
eq2 Z Z ≡ix f o () y
eq2 U U ≡ix f o tt tt = true

eq2 (I i) (I j)  ≡ix f o x y with ≡ix i j
eq2 (I i) (I j)  ≡ix f o x y | nothing   = false
eq2 (I i) (I .i) ≡ix f o x y | just refl = f i x y

eq2 (X R F) (X S G) ≡ix f o (some (y , y')) (some (y0 , y1)) = false -- TODO
eq2 (Y {I′ = J} g F) (Y {I′ = K} h G) ≡ix f o x y with ≡Ix J K
eq2 (Y g F) (Y h G) ≡ix f o x y | just refl = false -- TODO
eq2 (Y g F) (Y h G) ≡ix f o x y | nothing   = false

eq2 (Σ g) (Σ h) ≡ix f o (some {i1} x) (some {i2} y) = eq2 (g i1) (h i2) ≡ix f o x y

eq2 (F ⊕ G) (F' ⊕ G') ≡ix f o (inl x) (inl y) = eq2 F F' ≡ix f o x y
eq2 (F ⊕ G) (F' ⊕ G') ≡ix f o (inl x) (inr y) = false
eq2 (F ⊕ G) (F' ⊕ G') ≡ix f o (inr x) (inl y) = false
eq2 (F ⊕ G) (F' ⊕ G') ≡ix f o (inr x) (inr y) = eq2 G G' ≡ix f o x y

eq2 (F ⊗ G) (F' ⊗ G') ≡ix f o (x1 , x2) (y1 , y2) = eq2 F F' ≡ix f o x1 y1 ∧ eq2 G G' ≡ix f o x2 y2

eq2 (_⊚_ {M = M} F G) (_⊚_ {M = M'} F' G') ≡ix f o x y with ≡Ix M M'
...                               | nothing   = false
eq2 (F ⊚ G) (F' ⊚ G') ≡ix f o x y | just refl = eq2 F F' ≡ix (eq2 G G' ≡ix f) o x y

eq2 (! o) (! .o) ≡ix f .o refl refl = true

eq2 (Fix F) (Fix G) ≡ix f o ⟨ x ⟩ ⟨ y ⟩ = eq2 F G ≡ix (f ∦ eq2 (Fix F) (Fix G) ≡ix f) o x y

eq2 {r = r} {s = s} (EP C D e) (EP C' D' e') ≡ix f o x y with e r o | e' s o
eq2 (EP C D e) (EP C' D' e') ≡ix f o x y | ep from to | ep from' to' = eq2 C C' ≡ix f o (from x) (from' y)

eq2 _ _ _ _ _ _ _ = false

-- Semi-decidable equality
deqCode : {I O : IxCode} (C D : Code I O)
        → ({J : IxCode} → (i j : ⟪ J ⟫) → Maybe (i ≡ j))
        → Maybe (C ≡ D)
deqCode Z Z ≡ix = just refl
deqCode U U ≡ix = just refl
deqCode (I i) (I j) ≡ix with ≡ix i j
deqCode (I i) (I j) ≡ix | nothing = nothing
...                     | just p  = just (cong≡ I p)
deqCode (X R F) (X S G) ≡ix = nothing -- TODO
deqCode (Y f F) (Y g G) ≡ix = nothing -- TODO
deqCode (F ⊕ F') (G ⊕ G') ≡ix = {!!}
deqCode (F ⊗ F') (G ⊗ G') ≡ix = {!!}
deqCode (F ⊚ F') (G ⊚ G') ≡ix = {!!}
deqCode (! o) (! o') ≡ix = {!!}
deqCode (Σ f) (Σ g) ≡ix = {!!}
deqCode (Fix F) (Fix G) ≡ix = {!!}
deqCode (EP C1 D1 e1) (EP C2 D2 e2) ≡ix = {!!}
deqCode _ _ _ = nothing

deq : {I O : IxCode} {r s : Indexed I} (C D : Code I O)
    → ({I : IxCode} → (i j : ⟪ I ⟫) → Maybe (i ≡ j))
    → (∀ i → r i → s i → Maybe (r i ≡ s i))
    → (o : ⟪ O ⟫) → ⟦ C ⟧ r o → ⟦ D ⟧ s o
    → Maybe (⟦ C ⟧ r o ≡ ⟦ D ⟧ s o)

deq Z Z ≡ix f o () _
deq U U ≡ix f o tt tt = just refl

deq (I i) (I j)  ≡ix f o x y with ≡ix i j
deq (I i) (I j)  ≡ix f o x y | nothing   = nothing
deq (I i) (I .i) ≡ix f o x y | just refl = f i x y --f i x y

deq (X R F) (X S G) ≡ix f o (some (y , y')) (some (y0 , y1)) = nothing -- TODO
deq (Y {I′ = J} g F) (Y {I′ = K} h G) ≡ix f o x y with ≡Ix J K
deq (Y g F) (Y h G) ≡ix f o x y | just refl = nothing -- TODO
deq (Y g F) (Y h G) ≡ix f o x y | nothing   = nothing

deq (Σ g) (Σ h) ≡ix f o (some {i1} x) (some {i2} y) = mapMaybe (cong≡ {!Σ ?!}) (deq (g i1) (h i2) ≡ix f o x y)

deq (F ⊕ G) (F' ⊕ G') ≡ix f o (inl x) (inl y) with ≡Ix {!!} {!!}
deq (F ⊕ G) (F' ⊕ G') ≡ix f o (inl x) (inl y) | p = {!!} --deq F F' ≡ix f o x y
deq (F ⊕ G) (F' ⊕ G') ≡ix f o (inl x) (inr y) = nothing
deq (F ⊕ G) (F' ⊕ G') ≡ix f o (inr x) (inl y) = nothing
deq (F ⊕ G) (F' ⊕ G') ≡ix f o (inr x) (inr y) = nothing --deq G G' ≡ix f o x y

deq (F ⊗ G) (F' ⊗ G') ≡ix f o (x1 , x2) (y1 , y2) = nothing --deq F F' ≡ix f o x1 y1 ∧ deq G G' ≡ix f o x2 y2

deq (_⊚_ {M = M} F G) (_⊚_ {M = M'} F' G') ≡ix f o x y with ≡Ix M M'
...                               | nothing   = nothing
deq (F ⊚ G) (F' ⊚ G') ≡ix f o x y | just refl = nothing --deq F F' ≡ix (deq G G' ≡ix f) o x y

deq (! o) (! .o) ≡ix f .o refl refl = nothing --true

deq (Fix F) (Fix G) ≡ix f o ⟨ x ⟩ ⟨ y ⟩ = nothing --deq F G ≡ix (f ∦ deq (Fix F) (Fix G) ≡ix f) o x y

deq {r = r} {s = s} (EP C D e) (EP C' D' e') ≡ix f o x y with e r o | e' s o
deq (EP C D e) (EP C' D' e') ≡ix f o x y | ep from to | ep from' to' = nothing --deq C C' ≡ix f o (from x) (from' y)

deq _ _ _ _ _ _ _ = nothing
