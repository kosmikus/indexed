{-# OPTIONS --no-termination-check #-}

module Regular2Multirec where

open import Relation.Binary.PropositionalEquality

import Regular
import Multirec
open import Data.Sum
open import Data.Product
open import Data.Unit

r2mC : Regular.Code → Multirec.Code ⊤
r2mC Regular.U         = Multirec.U
r2mC Regular.I         = Multirec.I tt
r2mC (Regular.K X)     = Multirec.K X
r2mC (Regular._⊕_ F G) = Multirec._⊕_ (r2mC F) (r2mC G)
r2mC (Regular._⊗_ F G) = Multirec._⊗_ (r2mC F) (r2mC G)

r2m : {R : Set}
    → (C : Regular.Code) → Regular.⟦_⟧ C R ≡ Multirec.⟦_⟧ (r2mC C) (λ _ → R) tt
r2m Regular.U         = refl
r2m Regular.I         = refl
r2m (Regular.K X)     = refl
r2m (Regular._⊕_ F G) = cong₂ _⊎_ (r2m F) (r2m G)
r2m (Regular._⊗_ F G) = cong₂ _×_ (r2m F) (r2m G)
