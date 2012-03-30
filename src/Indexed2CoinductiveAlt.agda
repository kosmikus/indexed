{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

-- In this case we use the K code of Coinductive to encode the
-- parameters and the tags, but nothing else.
-- Most things seem to work as before, but we cannot use Indexed._∥_
-- for the fixed points because those are indexed over Sets, whereas
-- now we work with functors indexed over Coinductive.Codes.
-- This means we cannot reuse lots of the infrastructure in Indexed.

-- It's not entirely clear to me how much closer this gets us from
-- removing --type-in-type, though.

module Indexed2CoinductiveAlt where

import Coinductive
import Indexed
open import Prelude


i2cC' : {I O : Set} → Indexed.Code I O → (I → Coinductive.Code) → (O → Coinductive.Code)
i2cC' Indexed.U r o = Coinductive.U
i2cC' (Indexed.I i) r o = r i
i2cC' (Indexed.! i) r o = Coinductive.K (o ≡ i)
i2cC' (Indexed.K X) r o = Coinductive.K X
i2cC' (Indexed._⊕_ F G) r o = Coinductive._⊕_ (i2cC' F r o) (i2cC' G r o)
i2cC' (Indexed._⊗_ F G) r o = Coinductive._⊗_ (i2cC' F r o) (i2cC' G r o)

i2cC' (Indexed._⊚_ F G) r o = Coinductive.R (♯ i2cC' F (i2cC' G r) o)

i2cC' (Indexed.Fix F)   r o = Coinductive.R (♯ i2cC' F [ r , i2cC' (Indexed.Fix F) r ] o)

i2cC : {I O : Set} → Indexed.Code I O → (I → Set) → (O → Coinductive.Code)
i2cC C r o = i2cC' C (Coinductive.K ∘ r) o


fromIndexed' : {I O : Set} (C : Indexed.Code I O) (r : I → Coinductive.Code) (o : O)
             → Indexed.⟦_⟧ C (Coinductive.⟦_⟧ ∘ r) o → Coinductive.⟦_⟧ (i2cC' C r o)
fromIndexed' Indexed.U r o z = Coinductive.tt
fromIndexed' (Indexed.I i) r o x = x
fromIndexed' (Indexed.! i) r o p = Coinductive.k p
fromIndexed' (Indexed.K X) r o x = Coinductive.k x
fromIndexed' (Indexed._⊕_ F G) r o (inj₁ x)  = Coinductive.inl (fromIndexed' F r o x)
fromIndexed' (Indexed._⊕_ F G) r o (inj₂ x)  = Coinductive.inr (fromIndexed' G r o x)
fromIndexed' (Indexed._⊗_ F G) r o (x ,, y ) = Coinductive._,_ (fromIndexed' F r o x)
                                                               (fromIndexed' G r o y)
fromIndexed' (Indexed._⊚_ F G) r o x = 
  Coinductive.rec (fromIndexed' F (i2cC' G r) o
                    (Indexed.map F (fromIndexed' G r) o x))

fromIndexed' (Indexed.Fix F) r o (Indexed.⟨_⟩ x) =
  Coinductive.rec (fromIndexed' F _ o
    (Indexed.map F ([_,_] Indexed.id⇉ (fromIndexed' (Indexed.Fix F) r)) o x))

fromIndexed : {I O : Set} (C : Indexed.Code I O) (r : I → Set) (o : O)
            → Indexed.⟦_⟧ C r o → Coinductive.⟦_⟧ (i2cC C r o)
fromIndexed C r o =   fromIndexed' C (Coinductive.K ∘ r)  o
                    ∘ Indexed.map C (λ _ → Coinductive.k) o


toIndexed' : {I O : Set} (C : Indexed.Code I O) (r : I → Coinductive.Code) (o : O)
           → Coinductive.⟦_⟧ (i2cC' C r o) → Indexed.⟦_⟧ C (Coinductive.⟦_⟧ ∘ r) o
toIndexed' Indexed.U r o x = tt
toIndexed' (Indexed.I y) r o x = x
toIndexed' (Indexed.! y) r o (Coinductive.k p) = p
toIndexed' (Indexed.K X) r o (Coinductive.k y) = y
toIndexed' (Indexed._⊕_ F G) r o (Coinductive.inl x) = inj₁ (toIndexed' F r o x)
toIndexed' (Indexed._⊕_ F G) r o (Coinductive.inr x) = inj₂ (toIndexed' G r o x)
toIndexed' (Indexed._⊗_ F G) r o (Coinductive._,_ x y) = toIndexed' F r o x ,, toIndexed' G r o y
toIndexed' (Indexed._⊚_ F G) r o (Coinductive.rec x) =
  Indexed.map F (toIndexed' G r) o (toIndexed' F (i2cC' G r) o x)
toIndexed' (Indexed.Fix F) r o (Coinductive.rec x) =
  Indexed.⟨_⟩ (Indexed.map F ([_,_] Indexed.id⇉ (toIndexed' (Indexed.Fix F) r)) o
                (toIndexed' F _ o x))

toIndexed : {I O : Set}
            (C : Indexed.Code I O) (r : I → Set) (o : O)
          → Coinductive.⟦_⟧ (i2cC C r o) → Indexed.⟦_⟧ C r o
toIndexed C r o = Indexed.map C (λ _ → unK) o ∘ toIndexed' C (Coinductive.K ∘ r) o
  where unK : ∀ {x} → Coinductive.⟦_⟧ (Coinductive.K x) → x
        unK (Coinductive.k x) = x

goal : {I O : Set} {F : Indexed.Code (I ⊎ O) O} {r : I → Coinductive.Code} (i : I ⊎ O)
  (x'
   : Indexed._∣_ (λ x0 → Coinductive.⟦_⟧ (r x0))
     (Indexed.μ F (λ x0 → Coinductive.⟦_⟧ (r x0))) i)
  →
  [_,_] {C = λ z → Indexed._∣_ (Coinductive.⟦_⟧ ∘ r) (Indexed.μ F (Coinductive.⟦_⟧ ∘ r)) z → Indexed._∣_ (Coinductive.⟦_⟧ ∘ r) (Indexed.μ F (Coinductive.⟦_⟧ ∘ r)) z} (Indexed._⇉∘_ Indexed.id⇉ Indexed.id⇉)
  (λ ix z →
     Indexed._⇉∘_ (toIndexed' (Indexed.Fix F) r)
     (fromIndexed' (Indexed.Fix F) r) ix z)
  i x'
  ≡
  Indexed._⇉∘_ ([_,_] {C = λ z → Coinductive.⟦_⟧ ([ r , i2cC' (Indexed.Fix F) r ] z) → Indexed._∣_ (Coinductive.⟦_⟧ ∘ r) (Indexed.μ F (Coinductive.⟦_⟧ ∘ r)) z} Indexed.id⇉  (toIndexed' (Indexed.Fix F) r))
  ([_,_] {C = λ z → Indexed._∣_ (Coinductive.⟦_⟧ ∘ r)
                      (Indexed.μ F (Coinductive.⟦_⟧ ∘ r)) z → Coinductive.⟦_⟧ ([ r , i2cC' (Indexed.Fix F) r ] z)} Indexed.id⇉ (fromIndexed' (Indexed.Fix F) r)) i x'
goal (inj₁ i) x = refl
goal (inj₂ i) x = refl


open ≡-Reasoning

iso₁ : {I O : Set} (C : Indexed.Code I O) (r : I → Coinductive.Code)
     → Indexed._≅_ ((Indexed._⇉∘_ (toIndexed' C r) (fromIndexed' C r))) Indexed.id⇉
iso₁ Indexed.U r o tt = refl
iso₁ (Indexed.I y) r o x = refl
iso₁ (Indexed.! y) r o x = refl
iso₁ (Indexed.K X) r o x = refl
iso₁ (Indexed._⊕_ F G) r o (inj₁ x) = cong inj₁ (iso₁ F r o x)
iso₁ (Indexed._⊕_ F G) r o (inj₂ x) = cong inj₂ (iso₁ G r o x)
iso₁ (Indexed._⊗_ F G) r o (x ,, y) = cong₂ _,,_ (iso₁ F r o x) (iso₁ G r o y)

iso₁ (Indexed._⊚_ F G) r o x = begin

    Indexed.map F (toIndexed' G r) o
      (toIndexed' F (i2cC' G r) o
       (fromIndexed' F (i2cC' G r) o
        (Indexed.map F (fromIndexed' G r) o x)))

  ≡⟨ cong (Indexed.map F (toIndexed' G r) o) (iso₁ F _ o _) ⟩
 
    Indexed.map F (toIndexed' G r) o
      (Indexed.map F (fromIndexed' G r) o x)

  ≡⟨ sym (Indexed.map-∘ F (toIndexed' G r) (fromIndexed' G r) o x) ⟩

    Indexed.map F (Indexed._⇉∘_ (toIndexed' G r) (fromIndexed' G r)) o x

  ≡⟨ Indexed.map-cong F (iso₁ G r) o x ⟩

    Indexed.map F Indexed.id⇉ o x

  ≡⟨ Indexed.map-id F o x ⟩

    x ∎

iso₁ {I} {O} (Indexed.Fix F) r o (Indexed.⟨_⟩ x) = cong Indexed.⟨_⟩ $ begin

    Indexed.map F [ Indexed.id⇉ , toIndexed' (Indexed.Fix F) r ] o
      (toIndexed' F [ r , i2cC' (Indexed.Fix F) r ] o
       (fromIndexed' F [ r , i2cC' (Indexed.Fix F) r ] o
        (Indexed.map F [ Indexed.id⇉ , fromIndexed' (Indexed.Fix F) r ] o
         x)))

  ≡⟨ cong (Indexed.map F [ Indexed.id⇉ , toIndexed' (Indexed.Fix F) r ] o) (iso₁ F _ o _) ⟩

    Indexed.map F [ Indexed.id⇉ , toIndexed' (Indexed.Fix F) r ] o
      (Indexed.map F [ Indexed.id⇉ , fromIndexed' (Indexed.Fix F) r ] o x)

  ≡⟨ sym (Indexed.map-∘ F [ Indexed.id⇉ , toIndexed' (Indexed.Fix F) r ]
                          [ Indexed.id⇉ , fromIndexed' (Indexed.Fix F) r ] o x) ⟩

    Indexed.map F (Indexed._⇉∘_ [ Indexed.id⇉ , toIndexed' (Indexed.Fix F) r ]
                                [ Indexed.id⇉ , fromIndexed' (Indexed.Fix F) r ]) o x

  ≡⟨ sym (Indexed.map-cong F goal o x) ⟩

    Indexed.map F [ Indexed._⇉∘_ Indexed.id⇉ Indexed.id⇉
                  , Indexed._⇉∘_ (toIndexed' (Indexed.Fix F) r)
                                 (fromIndexed' (Indexed.Fix F) r) ] o x

  ≡⟨ Indexed.map-cong F (Indexed.[,]-cong (λ _ _ → refl) (iso₁ (Indexed.Fix F) r)) o x ⟩

    Indexed.map F ([ Indexed.id⇉ , Indexed.id⇉ ]) o x

  ≡⟨ Indexed.map-cong F Indexed.[,]-id o x ⟩

    Indexed.map F Indexed.id⇉ o x

  ≡⟨ Indexed.map-id F o x ⟩

    x ∎

