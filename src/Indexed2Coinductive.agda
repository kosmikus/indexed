{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module Indexed2Coinductive where

import Coinductive
import Indexed
open import Prelude


--------------------------------------------------------------------------------
-- Code conversion
--------------------------------------------------------------------------------
i2cC' : {I O : Set}
     → Indexed.Code I O → (I → Set) → (O → Coinductive.Code)
i2cC' Indexed.U r o = Coinductive.U
i2cC' (Indexed.I i) r o = Coinductive.K (r i)
i2cC' (Indexed.! i) r o = Coinductive.K (o ≡ i)
i2cC' (Indexed.K X) r o = Coinductive.K X
i2cC' (Indexed._⊕_ F G) r o = Coinductive._⊕_ (i2cC' F r o) (i2cC' G r o)
i2cC' (Indexed._⊗_ F G) r o = Coinductive._⊗_ (i2cC' F r o) (i2cC' G r o)

i2cC' (Indexed._⊚_ F G) r o = Coinductive.R   (♯
  i2cC' F (Coinductive.⟦_⟧ ∘ i2cC' G r) o)

i2cC' (Indexed.Fix F)   r o = Coinductive.R   (♯
  i2cC' F (Indexed._∣_ r (Coinductive.⟦_⟧ ∘ i2cC' (Indexed.Fix F) r)) o)
{-
i2cC : {I O : Set}
      → Indexed.Code I O → (I → Set) → (O → Coinductive.Code)
i2cC C r o = i2cC' C (Coinductive.K ∘ r) o
-}


--------------------------------------------------------------------------------
-- From Indexed to Coinductive
--------------------------------------------------------------------------------
from' : {I O : Set}
        (C : Indexed.Code I O) (r : I → Set) (o : O)
      → Indexed.⟦_⟧ C r o → Coinductive.⟦_⟧ (i2cC' C r o)
from' Indexed.U r o z = Coinductive.tt
from' (Indexed.I i) r o x = Coinductive.k x
from' (Indexed.! i) r o x = Coinductive.k x
from' (Indexed.K X) r o x = Coinductive.k x
from' (Indexed._⊕_ F G) r o (inj₁ x) = Coinductive.inl (from' F r o x)
from' (Indexed._⊕_ F G) r o (inj₂ x) = Coinductive.inr (from' G r o x)
from' (Indexed._⊗_ F G) r o (x , y ) = Coinductive._,_ (from' F r o x)
                                                       (from' G r o y)
from' (Indexed._⊚_ F G) r o x = 
  Coinductive.rec (from' F (Coinductive.⟦_⟧ ∘ i2cC' G r) o
                    (Indexed.map F (from' G r) o x))

from' (Indexed.Fix F) r o (Indexed.⟨_⟩ x) =
  Coinductive.rec (from' F _ o
    (Indexed.map F (Indexed._∥_ (λ _ → id) (from' (Indexed.Fix F) r)) o x))
{-
from : {I O : Set}
       (C : Indexed.Code I O) (r : I → Set) (o : O)
     → Indexed.⟦_⟧ C r o → Coinductive.⟦_⟧ (i2cC C r o)
from C r o = from' C (Coinductive.K ∘ r)   o 
           ∘ Indexed.map C (λ _ → Coinductive.k) o
-}
--------------------------------------------------------------------------------
-- To Indexed from Coinductive
--------------------------------------------------------------------------------
to' : {I O : Set}
      (C : Indexed.Code I O) (r : I → Set) (o : O)
    → Indexed.⟦_⟧ C r o ← Coinductive.⟦_⟧ (i2cC' C r o)
to' Indexed.U     _ _ _ = tt
to' (Indexed.I _) _ _ (Coinductive.k x) = x
to' (Indexed.! _) _ _ (Coinductive.k x) = x
to' (Indexed.K _) _ _ (Coinductive.k x) = x

to' (Indexed._⊕_ F G) r o (Coinductive.inl x) = inj₁ (to' F r o x)
to' (Indexed._⊕_ F G) r o (Coinductive.inr x) = inj₂ (to' G r o x)
to' (Indexed._⊗_ F G) r o (Coinductive._,_ x y) = to' F r o x 
                                                , to' G r o y

to' (Indexed._⊚_ F G) r o (Coinductive.rec x) =
  Indexed.map F (to' G r) o (to' F (Coinductive.⟦_⟧ ∘ i2cC' G r) o x)

to' (Indexed.Fix F) r o (Coinductive.rec x) =  
  Indexed.⟨_⟩ (Indexed.map F (Indexed._∥_ (λ _ → id) (to' (Indexed.Fix F) r)) o
    (to' F _ o x))
{-
to : {I O : Set}
     (C : Indexed.Code I O) (r : I → Set) (o : O)
   → Indexed.⟦_⟧ C r o ← Coinductive.⟦_⟧ (i2cC C r o)
to C r o = Indexed.map C (λ _ → Coinductive.unk) o 
         ∘ to' C (Coinductive.K ∘ r) o
-}
--------------------------------------------------------------------------------
-- Proof 
--------------------------------------------------------------------------------
open ≡-Reasoning

iso₁ : {I O : Set} (C : Indexed.Code I O) (r : I → Set)
     → Indexed._≅_ ((Indexed._⇉∘_ (to' C r) (from' C r))) Indexed.id⇉
iso₁  Indexed.U    r o tt = refl
iso₁ (Indexed.I y) r o _  = refl
iso₁ (Indexed.! y) r o _  = refl
iso₁ (Indexed.K X) r o _  = refl
iso₁ (Indexed._⊕_ F G) r o (inj₁ x) = cong inj₁ (iso₁ F r o x)
iso₁ (Indexed._⊕_ F G) r o (inj₂ x) = cong inj₂ (iso₁ G r o x)
iso₁ (Indexed._⊗_ F G) r o (x , y)  = cong₂ _,_ (iso₁ F r o x) (iso₁ G r o y)
iso₁ (Indexed._⊚_ F G) r o x        = begin
    
    Indexed.map F (to' G r) o
      (to'    F (Coinductive.⟦_⟧ ∘ i2cC' G r) o
       (from' F (Coinductive.⟦_⟧ ∘ i2cC' G r) o
        (Indexed.map F (from' G r) o x)))
  
  ≡⟨ cong (Indexed.map F (to' G r) o) (iso₁ F _ o _) ⟩

     Indexed.map F (to'   G r) o
    (Indexed.map F (from' G r) o x)

  ≡⟨ sym (Indexed.map-∘ F (to' G r) (from' G r) o x) ⟩

    Indexed.map F (Indexed._⇉∘_ (to' G r) (from' G r)) o x

  ≡⟨ Indexed.map-cong F (iso₁ G r) o x ⟩

    Indexed.map F Indexed.id⇉ o x

  ≡⟨ Indexed.map-id F o x ⟩

    x ∎

iso₁ {I} {O} (Indexed.Fix F) r o (Indexed.⟨_⟩ x) = cong Indexed.⟨_⟩ $
  begin

    Indexed.map F (Indexed._∥_ Indexed.id⇉ (to' (Indexed.Fix F) r)) o
      ( to'   F (Indexed._∣_ r _) o
       (from' F (Indexed._∣_ r _) o
         (Indexed.map F (Indexed._∥_ Indexed.id⇉ (from' (Indexed.Fix F) r)) o x)))

  ≡⟨ cong (Indexed.map F (Indexed._∥_ Indexed.id⇉ (to' (Indexed.Fix F) r)) o) (iso₁ F _ o _) ⟩

    Indexed.map    F (Indexed._∥_ Indexed.id⇉ (to'   (Indexed.Fix F) r)) o
      (Indexed.map F (Indexed._∥_ Indexed.id⇉ (from' (Indexed.Fix F) r)) o x)

  ≡⟨ sym (Indexed.map-∘ F ((Indexed._∥_ Indexed.id⇉ (to'   (Indexed.Fix F) r)))
                           ((Indexed._∥_ Indexed.id⇉ (from' (Indexed.Fix F) r))) o x) ⟩

    Indexed.map F (Indexed._⇉∘_ (Indexed._∥_ Indexed.id⇉ (to'   (Indexed.Fix F) r))
                                (Indexed._∥_ Indexed.id⇉ (from' (Indexed.Fix F) r))) o x

  ≡⟨ sym (Indexed.map-cong F Indexed.∥∘ o x) ⟩

    Indexed.map F (Indexed._∥_ (Indexed._⇉∘_ Indexed.id⇉ Indexed.id⇉)
                               (Indexed._⇉∘_ (to' (Indexed.Fix F) r) (from' (Indexed.Fix F) r))) o x

  ≡⟨ cong (λ z → Indexed.map F (Indexed._∥_ z (Indexed._⇉∘_ (to' (Indexed.Fix F) r) (from' (Indexed.Fix F) r))) o x) refl ⟩

    Indexed.map F (Indexed._∥_ Indexed.id⇉
                               (Indexed._⇉∘_ (to' (Indexed.Fix F) r) (from' (Indexed.Fix F) r))) o x

  ≡⟨ Indexed.map-cong F (Indexed.∥cong (λ _ _ → refl) (iso₁ (Indexed.Fix F) r)) o x ⟩

    Indexed.map F (Indexed._∥_ Indexed.id⇉ Indexed.id⇉) o x

  ≡⟨ Indexed.map-cong F (Indexed.∥id (λ _ _ → refl) (λ _ _ → refl)) o x ⟩

    Indexed.map F Indexed.id⇉ o x

  ≡⟨ Indexed.map-id F o x ⟩

    x ∎
