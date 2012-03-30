{-# OPTIONS --no-termination-check #-}

module ZipWith where

open import Prelude
open import IxFun


-- 3-natural transformations with failure
_⇶_⇶_ : ∀ {I} → Indexed I → Indexed I → Indexed I → Set
r ⇶ s ⇶ t = forall i → r i → s i → Maybe (t i)

-- (Not quite) Identity 3-natural transformation with failure
id⇶ : {I : Set} {r : Indexed I} → r ⇶ r ⇶ r
id⇶ i x y = just x

-- Merging 3-natural transformations with failure
infixr 5 _∥₃_
_∥₃_ : {I J : Set} {r s t : Indexed I} {u v w : Indexed J}
        → (r ⇶ s ⇶ t) → (u ⇶ v ⇶ w) → ((r ∣ u) ⇶ (s ∣ v) ⇶ (t ∣ w))
(f ∥₃ g) (inl x) = f x
(f ∥₃ g) (inr y) = g y


zipWith : {I O : Set} {r s t : Indexed I} (C : Code I O)
        → r ⇶ s ⇶ t → ⟦ C ⟧ r ⇶ ⟦ C ⟧ s ⇶ ⟦ C ⟧ t
zipWith Z f o () y
zipWith U f o x y = just tt
zipWith (I i) f o x y = f i x y

-- I don't think we can do much better here...
zipWith (X R F) f o (some {o1} (x , x1)) (some {o2} (y , y1)) = nothing

zipWith (Y g F) f o x y = zipWith F (f ∘ g) o x y
zipWith (F ⊕ G) f o (inl y) (inl y') = mapMaybe inl (zipWith F f o y y')
zipWith (F ⊕ G) f o (inl y) (inr y') = nothing
zipWith (F ⊕ G) f o (inr y) (inl y') = nothing
zipWith (F ⊕ G) f o (inr y) (inr y') = mapMaybe inr (zipWith G f o y y')
zipWith (F ⊗ G) f o (x1 , x2) (y1 , y2) =       zipWith F f o x1 y1 >>= 
                                          λ x → zipWith G f o x2 y2 >>= 
                                          λ y → just (x , y)
zipWith (F ⊚ G) f o x y = zipWith F (zipWith G f) o x y
zipWith (! o) f .o refl refl = just refl

--
zipWith (Σ g) f o (some {i1} x) (some {i2} y) = nothing --mapMaybe some (zipWith (g i2) f o {!!} {!!})

zipWith (Fix F) f o ⟨ x ⟩ ⟨ y ⟩ =
  mapMaybe ⟨_⟩ (zipWith F (f ∥₃ zipWith (Fix F) f) o x y)

zipWith {r = r} {s = s} {t = t} (EP C D e) f o x y with e r o | e s o | e t o
zipWith (EP C D e) f o x y | ep f1 _ | ep f2 _ | ep _ to =
  mapMaybe to (zipWith C f o (f1 x) (f2 y))
