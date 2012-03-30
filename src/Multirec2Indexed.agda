{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module Multirec2Indexed where

open import Relation.Binary.PropositionalEquality

import Multirec
import Indexed
open import Prelude

m2iC : {Ix : Set} → Multirec.Code Ix → Indexed.Code (⊥ ⊎ Ix) Ix
m2iC Multirec.U         = Indexed.U
m2iC (Multirec.I i)     = Indexed.I (inj₂ i)
m2iC (Multirec.! i)     = Indexed.! i
m2iC (Multirec.K X)     = Indexed.K X
m2iC (Multirec._⊕_ F G) = Indexed._⊕_ (m2iC F) (m2iC G)
m2iC (Multirec._⊗_ F G) = Indexed._⊗_ (m2iC F) (m2iC G)

liftedAbsurd : ⊥ → Set
liftedAbsurd ()

↑_ : {Ix : Set} → Indexed.Indexed Ix → Indexed.Indexed (⊥ ⊎ Ix)
(↑ r) (inj₁ ())
(↑ r) (inj₂ i) = r i

⇑_ : {Ix : Set} {r s : Indexed.Indexed Ix} → Indexed._⇉_ r s
   → Indexed._⇉_ (↑ r) (↑ s)
(⇑ r) (inj₁ ())
(⇑ r) (inj₂ i) = r i

m2i : {Ix : Set} {r : Multirec.Indexed Ix} {i : Ix}
    → (C : Multirec.Code Ix) → Multirec.⟦_⟧ C r i ≡ Indexed.⟦_⟧ (m2iC C) (↑ r) i
m2i Multirec.U         = refl
m2i (Multirec.I i)     = refl
m2i (Multirec.! i)     = refl
m2i (Multirec.K X)     = refl
m2i (Multirec._⊕_ F G) = cong₂ _⊎_ (m2i F) (m2i G)
m2i (Multirec._⊗_ F G) = cong₂ _×_ (m2i F) (m2i G)

fromM : {Ix : Set} {r : Multirec.Indexed Ix} {i : Ix}
      → (C : Multirec.Code Ix) → Multirec.⟦_⟧ C r i → Indexed.⟦_⟧ (m2iC C) (↑ r) i 
fromM = {!!} -- trivial, from above

fromμM : {Ix : Set} → (C : Multirec.Code Ix) → (i : Ix)
       → Multirec.μ C i → Indexed.μ (m2iC C) (λ _ → ⊥) i
fromμM {Ix} C i (Multirec.⟨_⟩ x) = Indexed.⟨_⟩ (Indexed.map (m2iC C) g i (fromM C x)) where
  g : (ix : ⊥ ⊎ Ix) →
      (↑ λ x' → Multirec.μ C x') ix →
      Indexed._∣_ (λ x' → ⊥) (Indexed.μ (m2iC C) (λ x' → ⊥)) ix
  g (inj₁ ()) _
  g (inj₂ j) y = fromμM C j y
--  g = ⇑ (fromμM C)
