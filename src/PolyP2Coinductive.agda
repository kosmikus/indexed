{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module PolyP2Coinductive where

open import Prelude
import Coinductive
import PolyP


p2cC' : PolyP.Code → PolyP.Code → Set → Coinductive.Code
p2cC' C PolyP.U A = Coinductive.U
p2cC' C PolyP.I A = Coinductive.R (♯ p2cC' C C A)
p2cC' C PolyP.P A = Coinductive.K A
p2cC' C (PolyP.K X) A = Coinductive.K X
p2cC' C (PolyP._⊕_ F G) A = Coinductive._⊕_ (♯ p2cC' C F A) (♯ p2cC' C G A)
p2cC' C (PolyP._⊗_ F G) A = Coinductive._⊗_ (♯ p2cC' C F A) (♯ p2cC' C G A)
p2cC' C (PolyP._⊚_ F G) A = Coinductive.R (♯ p2cC' F F (Coinductive.⟦_⟧ (p2cC' C G A)))
{-
Consider also the following alternative interpretations of PolyP._⊚_:

p2cC' C (PolyP._⊚_ F G) A = Coinductive.R (♯ p2cC' C F (PolyP.μ G A))
p2cC' C (PolyP._⊚_ F G) A = Coinductive.K (PolyP.μ F (Coinductive.⟦_⟧ (p2cC' C G A)))

Both are incorrect. The one given above, as far as I can see, is the right one.
-}

p2cC : PolyP.Code → Set → Coinductive.Code
p2cC C A = p2cC' C C A


mutual
  fromPolyP : {A : Set} → (C : PolyP.Code) → (D : PolyP.Code)
            → PolyP.⟦_⟧ D A (PolyP.μ C A) → Coinductive.⟦_⟧ (p2cC' C D A)
  fromPolyP C PolyP.U _ = Coinductive.tt
  fromPolyP C PolyP.I x = Coinductive.rec (fromμPolyP C x)
  fromPolyP C PolyP.P x = Coinductive.k x
  fromPolyP C (PolyP.K X) x = Coinductive.k x
  fromPolyP C (PolyP._⊕_ F G) (inj₁ x) = Coinductive.inl (fromPolyP C F x)
  fromPolyP C (PolyP._⊕_ F G) (inj₂ x) = Coinductive.inr (fromPolyP C G x)
  fromPolyP C (PolyP._⊗_ F G) (x , y)  = Coinductive._,_ (fromPolyP C F x)
                                                         (fromPolyP C G y)
  fromPolyP C (PolyP._⊚_ F G) x =
    Coinductive.rec (fromμPolyP F (PolyP.pmap (fromPolyP C G) x))

  fromμPolyP : {A : Set} → (C : PolyP.Code)
             → PolyP.μ C A → Coinductive.⟦_⟧ (p2cC C A)
  fromμPolyP C (PolyP.⟨_⟩ x) = fromPolyP C C x


mutual
  toPolyP : {A : Set} → (C : PolyP.Code) → (D : PolyP.Code)
            → PolyP.⟦_⟧ D A (PolyP.μ C A) ← Coinductive.⟦_⟧ (p2cC' C D A)
  toPolyP C PolyP.U      _                  = tt
  toPolyP C PolyP.I     (Coinductive.rec x) = toμPolyP C x
  toPolyP C PolyP.P     (Coinductive.k   x) = x
  toPolyP C (PolyP.K X) (Coinductive.k   x) = x
  toPolyP C (PolyP._⊕_ F G) (Coinductive.inl x)   = inj₁ (toPolyP C F x)
  toPolyP C (PolyP._⊕_ F G) (Coinductive.inr x)   = inj₂ (toPolyP C G x)
  toPolyP C (PolyP._⊗_ F G) (Coinductive._,_ x y) = toPolyP C F x , toPolyP C G y
  toPolyP C (PolyP._⊚_ F G) (Coinductive.rec x)   =
    PolyP.pmap (toPolyP C G) (toμPolyP F x)

  toμPolyP : {A : Set} → (C : PolyP.Code)
           → PolyP.μ C A ← Coinductive.⟦_⟧ (p2cC C A)
  toμPolyP C z = PolyP.⟨_⟩ (toPolyP C C z)


-- To do: conversion proofs
