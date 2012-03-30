{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Regular2Coinductive where

open import Relation.Binary.PropositionalEquality

import Regular
import Coinductive
open import Prelude

-- Code conversion
r2cC' : Regular.Code → Regular.Code → Coinductive.Code
r2cC' C  Regular.U        = Coinductive.U
r2cC' C (Regular.K X)     = Coinductive.K    X
r2cC' C  Regular.I        = Coinductive.R   (♯ r2cC' C C)
r2cC' C (Regular._⊕_ F G) = Coinductive._⊕_ (r2cC' C F) (r2cC' C G)
r2cC' C (Regular._⊗_ F G) = Coinductive._⊗_ (r2cC' C F) (r2cC' C G)

r2cC : Regular.Code → Coinductive.Code
r2cC C = r2cC' C C

mutual
  fromRegular : (C : Regular.Code) → (D : Regular.Code)
              → Regular.⟦_⟧ D (Regular.μ C) → Coinductive.⟦_⟧ (r2cC' C D)
  fromRegular C  Regular.U    _ = Coinductive.tt
  fromRegular C (Regular.K X) x = Coinductive.k x
  fromRegular C  Regular.I    x = Coinductive.rec (fromμRegular C x)
  fromRegular C (Regular._⊕_ F G) (inj₁ x) = Coinductive.inl (fromRegular C F x)
  fromRegular C (Regular._⊕_ F G) (inj₂ x) = Coinductive.inr (fromRegular C G x)
  fromRegular C (Regular._⊗_ F G) (x , y)  = Coinductive._,_ (fromRegular C F x)
                                                             (fromRegular C G y)

  fromμRegular : (C : Regular.Code)
               → Regular.μ C → Coinductive.⟦_⟧ (r2cC C)
  fromμRegular C (Regular.⟨_⟩ x) = fromRegular C C x


mutual
  toRegular : (C : Regular.Code) → (D : Regular.Code)
            → Regular.⟦_⟧ D (Regular.μ C) ← Coinductive.⟦_⟧ (r2cC' C D)
  toRegular C  Regular.U         _                    = tt
  toRegular C  Regular.I        (Coinductive.rec x)   = toμRegular C x
  toRegular C (Regular.K X)     (Coinductive.k   x)   = x
  toRegular C (Regular._⊕_ F G) (Coinductive.inl x)   = inj₁ (toRegular C F x)
  toRegular C (Regular._⊕_ F G) (Coinductive.inr x)   = inj₂ (toRegular C G x)
  toRegular C (Regular._⊗_ F G) (Coinductive._,_ x y) = toRegular C F x , toRegular C G y

  toμRegular : (C : Regular.Code)
               → Regular.μ C ← Coinductive.⟦_⟧ (r2cC C)
  toμRegular C x = Regular.⟨_⟩ (toRegular C C x)


-- To do: conversion proofs
