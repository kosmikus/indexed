{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Regular2PolyP where

import Regular
import PolyP
open import Prelude

-- Code equivalence
r2pC : Regular.Code → PolyP.Code
r2pC Regular.U         = PolyP.U
r2pC Regular.I         = PolyP.I
r2pC (Regular.K X)     = PolyP.K X
r2pC (Regular._⊕_ F G) = PolyP._⊕_ (r2pC F) (r2pC G)
r2pC (Regular._⊗_ F G) = PolyP._⊗_ (r2pC F) (r2pC G)

r2p : {R : Set}
    → (C : Regular.Code) → Regular.⟦_⟧ C R ≡ PolyP.⟦_⟧ (r2pC C) ⊥ R
r2p (Regular.U)       = refl
r2p (Regular.I)       = refl
r2p (Regular.K X)     = refl
r2p (Regular._⊕_ F G) = cong₂ _⊎_ (r2p F) (r2p G)
r2p (Regular._⊗_ F G) = cong₂ _×_ (r2p F) (r2p G)

fromRegular : {R : Set} (C : Regular.Code)
            → Regular.⟦_⟧ C R → PolyP.⟦_⟧ (r2pC C) ⊥ R
--fromRegular C = ≡→ (r2p C)
fromRegular  Regular.U        = id
fromRegular  Regular.I        = id
fromRegular (Regular.K X)     = id
fromRegular (Regular._⊕_ F G) = [ inj₁ ∘ fromRegular F  , inj₂ ∘ fromRegular G  ]
fromRegular (Regular._⊗_ F G) = < fromRegular F ∘ proj₁ , fromRegular G ∘ proj₂ >
{-
fromRegular C = Regular.foldRegular C {λ C → PolyP.⟦_⟧ (r2pC C) _ _}
                  tt id (λ _ x → x) (λ _ _ → inj₁) (λ _ _ → inj₂) (λ _ _ → _,_)
-}

fromμRegular : (C : Regular.Code)
             → Regular.μ C → PolyP.μ (r2pC C) ⊥
fromμRegular C (Regular.⟨_⟩ x) = 
  PolyP.⟨_⟩ (fromRegular C (Regular.map C (fromμRegular C) x))


toRegular : {R : Set} (C : Regular.Code)
          → Regular.⟦_⟧ C R ← PolyP.⟦_⟧ (r2pC C) ⊥ R
--toRegular C = ≡← (r2p C)
toRegular  Regular.U        = id
toRegular  Regular.I        = id
toRegular (Regular.K X)     = id
toRegular (Regular._⊕_ F G) = [ inj₁ ∘ toRegular F  , inj₂ ∘ toRegular G  ]
toRegular (Regular._⊗_ F G) = < toRegular F ∘ proj₁ , toRegular G ∘ proj₂ >

toμRegular : (C : Regular.Code)
           → Regular.μ C ← PolyP.μ (r2pC C) ⊥
toμRegular C (PolyP.⟨_⟩ x) =
  Regular.⟨_⟩ (toRegular C (PolyP.map (r2pC C) id (toμRegular C) x))

-- Fixed-points isomorphism
iso₁ : {R : Set} (C : Regular.Code) {x : Regular.⟦_⟧ C R}
       → toRegular C (fromRegular C x) ≡ x
--iso₁ C = ≡₁ (r2p C)
iso₁ Regular.U     = refl
iso₁ Regular.I     = refl
iso₁ (Regular.K X) = refl
iso₁ (Regular._⊕_ F G) {inj₁ x} = cong inj₁ (iso₁ F)
iso₁ (Regular._⊕_ F G) {inj₂ x} = cong inj₂ (iso₁ G)
iso₁ (Regular._⊗_ F G) {x , y}  = cong₂ _,_ (iso₁ F) (iso₁ G)

iso₂ : {R : Set} (C : Regular.Code) {x : PolyP.⟦_⟧ (r2pC C) ⊥ R}
       → fromRegular C (toRegular C x) ≡ x
--iso₂ C = ≡₂ (r2p C)
iso₂ Regular.U     = refl
iso₂ Regular.I     = refl
iso₂ (Regular.K X) = refl
iso₂ (Regular._⊕_ F G) {inj₁ x} = cong inj₁ (iso₂ F)
iso₂ (Regular._⊕_ F G) {inj₂ x} = cong inj₂ (iso₂ G)
iso₂ (Regular._⊗_ F G) {x , y}  = cong₂ _,_ (iso₂ F) (iso₂ G)


lemma₁ : {R₁ R₂ : Set} (C : Regular.Code)
         {f : R₁ → R₂} (x : PolyP.⟦_⟧ (r2pC C) ⊥ R₁)
       → toRegular C (PolyP.map (r2pC C) id f x)
       ≡ Regular.map C f (toRegular C x)
lemma₁ Regular.U     _ = refl
lemma₁ Regular.I     _ = refl
lemma₁ (Regular.K X) _ = refl
lemma₁ (Regular._⊕_ F G) (inj₁ x) = cong inj₁ (lemma₁ F x)
lemma₁ (Regular._⊕_ F G) (inj₂ x) = cong inj₂ (lemma₁ G x)
lemma₁ (Regular._⊗_ F G) (x , y)  = cong₂ _,_ (lemma₁ F x) (lemma₁ G y)

open ≡-Reasoning

isoμ₁ : (C : Regular.Code) (x : Regular.μ C)
      → toμRegular C (fromμRegular C x) ≡ x
isoμ₁ C (Regular.⟨_⟩ x) = cong Regular.⟨_⟩ $
      begin

    toRegular C (PolyP.map (r2pC C) id (toμRegular C)
      (fromRegular C (Regular.map C (fromμRegular C) x)))

      ≡⟨ lemma₁ C _ ⟩ 

    Regular.map C (toμRegular C) (toRegular C 
      (fromRegular C (Regular.map C (fromμRegular C) x)))
 
      ≡⟨ cong (Regular.map C (toμRegular C)) (iso₁ C) ⟩

    Regular.map C (toμRegular C)
      (Regular.map C (fromμRegular C) x)

      ≡⟨ Regular.map∘ C ⟩

    Regular.map C (toμRegular C ∘ fromμRegular C) x

      ≡⟨ Regular.map∀ {C} _ _ (isoμ₁ C) x ⟩

    Regular.map C id x

      ≡⟨ Regular.mapId C ⟩

    x ∎

isoμ₂ : (C : Regular.Code) (x : PolyP.μ (r2pC C) ⊥)
      → fromμRegular C (toμRegular C x) ≡ x
isoμ₂ C (PolyP.⟨_⟩ x) = cong PolyP.⟨_⟩ $
    begin

  fromRegular C (Regular.map C (fromμRegular C)
    (toRegular C (PolyP.map (r2pC C) id (toμRegular C) x)))
    
    ≡⟨ cong (λ z → fromRegular C (Regular.map C (fromμRegular C) z)) (lemma₁ C _) ⟩

  fromRegular C (Regular.map C (fromμRegular C)
    (Regular.map C (toμRegular C) (toRegular C x)))

    ≡⟨ cong (fromRegular C) (Regular.map∘ C) ⟩

  fromRegular C
    (Regular.map C (fromμRegular C ∘ toμRegular C) (toRegular C x))

    ≡⟨ cong (fromRegular C) (Regular.map∀ {C} _ _ (isoμ₂ C) _) ⟩

  fromRegular C (Regular.map C id (toRegular C x))

    ≡⟨ cong (fromRegular C) (Regular.mapId C) ⟩

  fromRegular C (toRegular C x)

    ≡⟨ iso₂ C ⟩

  x ∎
