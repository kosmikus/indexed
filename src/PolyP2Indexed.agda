{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module PolyP2Indexed where

open import Prelude

import PolyP
import Indexed


p2iC : PolyP.Code → Indexed.Code (⊤ ⊎ ⊤) ⊤
p2iC PolyP.U = Indexed.U
p2iC PolyP.P = Indexed.I (inj₁ tt)
p2iC PolyP.I = Indexed.I (inj₂ tt)
p2iC (PolyP.K X) = Indexed.K X
p2iC (PolyP._⊕_ F G) = Indexed._⊕_ (p2iC F) (p2iC G)
p2iC (PolyP._⊗_ F G) = Indexed._⊗_ (p2iC F) (p2iC G)
p2iC (PolyP._⊚_ F G) = Indexed._⊚_ (Indexed.Fix (p2iC F)) (p2iC G)


fromP : {A R : Set}
      → (C : PolyP.Code) → PolyP.⟦_⟧ C A R
      → Indexed.⟦_⟧ (p2iC C) (Indexed._∣_ (λ _ → A) (λ _ → R)) tt
fromP PolyP.U tt = tt
fromP PolyP.I y = y
fromP PolyP.P y = y
fromP (PolyP.K X) y = y
fromP (PolyP._⊕_ F G) (inj₁ x) = inj₁ (fromP F x)
fromP (PolyP._⊕_ F G) (inj₂ y) = inj₂ (fromP G y)
fromP (PolyP._⊗_ F G) (x , y) = fromP F x , fromP G y
fromP (PolyP._⊚_ F G) (PolyP.⟨_⟩ x) =
  Indexed.⟨_⟩ (Indexed.bimap (p2iC F) (λ _ → fromP G) (λ _ → fromP (PolyP._⊚_ F G)) tt (fromP F x))

fromμP : {A : Set} → (C : PolyP.Code) → PolyP.μ C A
       → Indexed.⟦_⟧ (p2iC C) (Indexed._∣_ (λ _ → A) (Indexed.μ (p2iC C) (λ _ → A))) tt
fromμP C (PolyP.⟨_⟩ y) = Indexed.bimap (p2iC C) 
                           (const id) (λ _ → Indexed.⟨_⟩ ∘ fromμP C)
                           tt (fromP C y)


toP : {A R : Set} (C : PolyP.Code)
    → Indexed.⟦_⟧ (p2iC C) (Indexed._∣_ (λ _ → A) (λ _ → R)) tt → PolyP.⟦_⟧ C A R
toP PolyP.U x = tt
toP PolyP.I x = x
toP PolyP.P x = x
toP (PolyP.K X) x = x
toP (PolyP._⊕_ F G) (inj₁ x) = inj₁ (toP F x)
toP (PolyP._⊕_ F G) (inj₂ y) = inj₂ (toP G y)
toP (PolyP._⊗_ F G) (x , y) = toP F x , toP G y
toP {A} {R} (PolyP._⊚_ F G) (Indexed.⟨_⟩ x) = 
  PolyP.⟨_⟩ (toP F (Indexed.bimap (p2iC F) (λ _ → toP G) (λ _ → toP (PolyP._⊚_ F G)) tt x))

mutual
  inn : {A : Set} → (C : PolyP.Code) → (i : ⊤) → Indexed.μ (p2iC C) (λ _ → A) tt → PolyP.μ C A
  inn C _ (Indexed.⟨_⟩ y) = toμP C y

  toμP : {A : Set} → (C : PolyP.Code)
       → Indexed.⟦_⟧ (p2iC C) (Indexed._∣_ (λ _ → A) (Indexed.μ (p2iC C) (λ _ → A))) tt 
       → PolyP.μ C A
  toμP C x = PolyP.⟨_⟩ (toP C (Indexed.bimap (p2iC C) (const id) (inn C) tt x))


open ≡-Reasoning

isoP₁ : {A R : Set} → (C : PolyP.Code)
      → (x : PolyP.⟦_⟧ C A R) → toP {A} {R} C (fromP C x) ≡ x
isoP₁ PolyP.U tt = refl
isoP₁ PolyP.I _ = refl
isoP₁ PolyP.P _ = refl
isoP₁ (PolyP.K X) _ = refl
isoP₁ (PolyP._⊕_ F G) (inj₁ x) = cong inj₁ (isoP₁ F x)
isoP₁ (PolyP._⊕_ F G) (inj₂ x) = cong inj₂ (isoP₁ G x)
isoP₁ (PolyP._⊗_ F G) (x , y)  = cong₂ _,_ (isoP₁ F x) (isoP₁ G y)
isoP₁ {A} {R} (PolyP._⊚_ F G) (PolyP.⟨_⟩ x) = cong PolyP.⟨_⟩ $
  begin

    (toP F (Indexed.map (p2iC F) (Indexed._∥_ (λ _ → toP   G) (λ _ → toP   (PolyP._⊚_ F G))) tt
           (Indexed.map (p2iC F) (Indexed._∥_ (λ _ → fromP G) (λ _ → fromP (PolyP._⊚_ F G))) tt
    (fromP F x))))

  ≡⟨ cong (toP F) (sym (Indexed.map-∘ (p2iC F) _ _ tt (fromP F x))) ⟩

    (toP F (Indexed.map (p2iC F) (Indexed._⇉∘_ (Indexed._∥_ (λ _ → toP   G) (λ _ → toP   (PolyP._⊚_ F G)))
                                               (Indexed._∥_ (λ _ → fromP G) (λ _ → fromP (PolyP._⊚_ F G)))) tt
    (fromP F x)))

  ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (λ i x → sym (Indexed.∥∘ i x)) tt (fromP F x)) ⟩

    (toP F (Indexed.map (p2iC F) (Indexed._∥_
      (Indexed._⇉∘_ (λ _ → toP  G)              (λ _ → fromP G))
      (Indexed._⇉∘_ (λ _ → toP (PolyP._⊚_ F G)) (λ _ → fromP (PolyP._⊚_ F G)))) tt
    (fromP F x)))

  ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (Indexed.∥cong (λ _ → isoP₁ G) (λ _ _ → refl)) tt (fromP F x)) ⟩

    (toP F (Indexed.map (p2iC F) (Indexed._∥_
      Indexed.id⇉
      (Indexed._⇉∘_ (λ _ → toP (PolyP._⊚_ F G)) (λ _ → fromP (PolyP._⊚_ F G)))) tt
    (fromP F x)))

  ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (Indexed.∥cong (λ _ _ → refl) (λ _ → isoP₁ (PolyP._⊚_ F G))) tt (fromP F x)) ⟩

    (toP F (Indexed.map (p2iC F) (Indexed._∥_
      Indexed.id⇉
      Indexed.id⇉) tt
    (fromP F x)))

  ≡⟨ cong (toP F) (Indexed.map-cong (p2iC F) (Indexed.∥id (λ _ _ → refl) (λ _ _ → refl)) tt (fromP F x)) ⟩

    (toP F (Indexed.map (p2iC F) Indexed.id⇉ tt (fromP F x)))

  ≡⟨ cong (toP F) (Indexed.map-id (p2iC F) tt (fromP F x)) ⟩

    (toP F (fromP F x))

  ≡⟨ isoP₁ F x ⟩

    x ∎


isoμP₁ : {A : Set} → (C : PolyP.Code)
       → (x : PolyP.μ C A) → toμP {A} C (fromμP C x) ≡ x
isoμP₁ {A} C (PolyP.⟨_⟩ x) = cong PolyP.⟨_⟩ $
  begin

    toP C
     (Indexed.map (p2iC C)
      (Indexed._∥_ (λ _ → id) (inn C)) tt
       (Indexed.map (p2iC C)
        (Indexed._∥_ (λ _ → id) (λ _ y → Indexed.⟨_⟩ (fromμP C y))) tt
         (fromP C x)))

  ≡⟨ cong (toP C) (sym (Indexed.map-∘ (p2iC C) _ _ tt (fromP C x))) ⟩

    toP C
     (Indexed.map (p2iC C)
      (Indexed._⇉∘_ (Indexed._∥_ (λ _ → id) (inn C))
                    (Indexed._∥_ (λ _ → id) (λ _ y → Indexed.⟨_⟩ (fromμP C y)))) tt
         (fromP C x))

  ≡⟨ cong (toP C) (Indexed.map-cong (p2iC C) (λ i y → sym (Indexed.∥∘ i y)) tt (fromP C x)) ⟩

    toP C
     (Indexed.map (p2iC C)
      (Indexed._∥_ (Indexed._⇉∘_ (λ _ → id) (λ _ → id))
                   (Indexed._⇉∘_ (inn C) (λ _ y → Indexed.⟨_⟩ (fromμP C y)))) tt
         (fromP C x))

  ≡⟨ cong (toP C) (Indexed.map-cong (p2iC C) (Indexed.∥cong (λ _ _ → refl) (λ _ y → isoμP₁ C y)) tt (fromP C x)) ⟩

    toP C
     (Indexed.map (p2iC C)
      (Indexed._∥_ Indexed.id⇉ Indexed.id⇉) tt
         (fromP C x))

  ≡⟨ cong (toP C) (Indexed.map-cong (p2iC C) (Indexed.∥id (λ _ _ → refl) (λ _ _ → refl)) tt (fromP C x)) ⟩

    toP C
     (Indexed.map (p2iC C) Indexed.id⇉ tt
         (fromP C x))

  ≡⟨ cong (toP C) (Indexed.map-id (p2iC C) tt (fromP C x)) ⟩

    toP C (fromP C x)

  ≡⟨ isoP₁ C x ⟩

    x ∎
