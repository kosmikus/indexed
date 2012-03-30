{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}

module IxFunProofs where

open import Prelude

----------------------------------------------------------------------
-- The universe of indexed functors
----------------------------------------------------------------------

-- Indexed family.
Indexed : Set → Set₁
Indexed I = I → Set

-- Natural transformations.
_⇉_ : ∀ {I} → Indexed I → Indexed I → Set
r ⇉ s = forall i → r i → s i

-- Identity natural transformation.
id⇉ : {I : Set} {r : Indexed I} → r ⇉ r
id⇉ i = id

-- Composing natural transformations
_⇉∘_ : {I : Set} {r s t : Indexed I} → s ⇉ t → r ⇉ s → r ⇉ t
(f ⇉∘ g) i x = f i (g i x)

-- Special case of const.
T : Set → Indexed ⊤
T A tt = A

-- Lifting a function to a (unit-type-indexed) natural transformation.
↑ : ∀ {A B : Set} → (A → B) → (T A ⇉ T B)
↑ f tt x = f x

-- Merging indexed families.
infixr 5 _∣_
_∣_ : ∀ {I J} → Indexed I → Indexed J → Indexed (I + J)
(r ∣ s) (inl i) = r i
(r ∣ s) (inr j) = s j

-- Merging natural transformations.
infixr 5 _∥_
_∥_ : {I J : Set} {r u : Indexed I} {s v : Indexed J} →
     (r ⇉ u) → (s ⇉ v) → ((r ∣ s) ⇉ (u ∣ v))
_∥_ f g (inl x) = f x
_∥_ f g (inr y) = g y

----------------------------------------------------------------------
-- Properties of morphism merging
----------------------------------------------------------------------
infix 4 _≗_
_≗_ : ∀ {I : Set}{r s : Indexed I} (f g : r ⇉ s) → Set
f ≗ g = ∀ i x → f i x ≡ g i x

∥-cong : {I J : Set}{r u : Indexed I}{s v : Indexed J}{f₁ f₂ : r ⇉ u}{g₁ g₂ : s ⇉ v} →
         f₁ ≗ f₂ → g₁ ≗ g₂ → (f₁ ∥ g₁) ≗ (f₂ ∥ g₂)
∥-cong if ig (inl i) x = if i x
∥-cong if ig (inr j) x = ig j x

∥-id : {I J : Set} {r : Indexed I} {s : Indexed J}{f : r ⇉ r}{g : s ⇉ s} →
       f ≗ id⇉ → g ≗ id⇉ → (f ∥ g) ≗ id⇉
∥-id if ig (inl i) x = if i x
∥-id if ig (inr j) x = ig j x

∥-∘ : {I J : Set}{r₁ s₁ t₁ : Indexed I}{r₂ s₂ t₂ : Indexed J} → 
      {f₁ : s₁ ⇉ t₁}{g₁ : r₁ ⇉ s₁}{f₂ : s₂ ⇉ t₂}{g₂ : r₂ ⇉ s₂} →
      (f₁ ⇉∘ g₁ ∥ f₂ ⇉∘ g₂) ≗ ((f₁ ∥ f₂) ⇉∘ (g₁ ∥ g₂))
∥-∘ (inl i) x = refl
∥-∘ (inr j) x = refl

-- Binary relations (move to prelude)
Rel : Set → Set → Set₁
Rel A B = A → B → Set

-- Indexed functors
_▷_ : Set → Set → Set₁
I ▷ O = Indexed I → Indexed O

-- Codes for indexed functors
infixr 3 _⊕_
infixr 4 _⊗_
infixr 5 _⊚_

data Wrap {I I′ : Set} (f : I′ → I) (r : Indexed I) : Indexed I′ where
  wrap : {i′ : I′} → r (f i′) → Wrap f r i′

mapWrap : {I I′ : Set} {r : Indexed I} {s : Indexed I} {f : I′ → I}
        → (r ⇉ s) → (Wrap f r ⇉ Wrap f s)
mapWrap f _ (wrap r) = wrap (f _ r)

-- The proofs are not optional
infix 3 _≃_
record _≃_ (A B : Set) : Set where
  field
    from  : A → B
    to    : B → A
    iso₁  : ∀ {x} → to (from x) ≡ x
    iso₂  : ∀ {x} → from (to x) ≡ x


mutual
  data Code : Set → Set → Set₁ where
    Z   : ∀ {I O} → Code I O
    U   : ∀ {I O} → Code I O
    I   : ∀ {I O} → (i : I) → Code I O
    X   : ∀ {I O O′} → (O → O′) → (F : Code I O′) → Code I O
    Y   : ∀ {I I′ O} → (I′ → I) → (F : Code I′ O) → Code I O
    _⊕_ : ∀ {I O} → (F : Code I O) → (G : Code I O) → Code I O
    _⊗_ : ∀ {I O} → (F : Code I O) → (G : Code I O) → Code I O
    _⊚_ : ∀ {I M O} → (F : Code M O) → (G : Code I M) → Code I O
    !   : ∀ {I O} → (o′ : O) → Code I O
    Σ  : ∀ {I O} {C : Code ⊥ ⊤} → (⟦ C ⟧ (λ _ → ⊤) tt → Code I O) → Code I O
    Fix : ∀ {I O} → (F : Code (I + O) O) → Code I O
    EP  : ∀ {I O} → (C : Code I O) → (D : I ▷ O)
                  → (e : (r : Indexed I) → (o : O) → D r o ≃ ⟦ C ⟧ r o)
                  → Code I O

-- Interpretation of codes as indexed functors.
  data μ {I O : Set} (F : Code (I + O) O) (r : Indexed I) (o : O) : Set where
    ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

  ⟦_⟧ : ∀ {I O : Set} → Code I O → I ▷ O
  ⟦ Z     ⟧    r o = ⊥
  ⟦ U     ⟧    r o = ⊤
  ⟦ I i   ⟧    r o = r i
  ⟦ X f F ⟧    r o = ⟦ F ⟧ r (f o)
  ⟦ Y f F ⟧    r o = ⟦ F ⟧ (r ∘ f) o
  ⟦ F ⊕ G ⟧    r o = ⟦ F ⟧ r o + ⟦ G ⟧ r o
  ⟦ F ⊗ G ⟧    r o = ⟦ F ⟧ r o × ⟦ G ⟧ r o
  ⟦ F ⊚ G ⟧    r o = ⟦ F ⟧ (⟦ G ⟧ r) o
  ⟦ ! o′  ⟧    r o = o ≡ o′
  ⟦ Σ f  ⟧    r o = ∃ (λ i → ⟦ f i ⟧ r o)
  ⟦ Fix F ⟧    r o = μ F r o
  ⟦ EP C D e ⟧ r o = D r o

----------------------------------------------------------------------
-- Definition of map for indexed functors
----------------------------------------------------------------------

map : {I O : Set} {r s : Indexed I} (C : Code I O) →
      (r ⇉ s) → (⟦ C ⟧ r ⇉ ⟦ C ⟧ s)
map Z          f o ()
map U          f o x                   = x
map (I i)      f o x                   = f i x
map (X g F)    f o x                   = map F f (g o) x
map (Y g F)    f o x                   = map F (λ i → f (g i)) o x
map (F ⊕ G)    f o (inl x)             = inl (map F f o x)
map (F ⊕ G)    f o (inr y)             = inr (map G f o y)
map (F ⊗ G)    f o (x , y)             = map F f o x , map G f o y
map (F ⊚ G)    f o x                   = map F (map G f) o x
map (! o')     f o x                   = x
map (Σ g)     f o (some {i} x)        = some (map (g i) f o x)
map (Fix F)    f o ⟨ x ⟩               = ⟨ map F (f ∥ map (Fix F) f) o x ⟩

map {r = r} {s = s} (EP C D e) f o x with e r o , e s o
map (EP C _ _) f o x | ep₁ , ep₂ = _≃_.to ep₂ ((map C f o (_≃_.from ep₁ x)))

map-cong : {I O : Set}{r s : Indexed I}{f g : r ⇉ s}→
           (C : Code I O) → f ≗ g →
           map C f ≗ map C g
map-cong Z          ip i ()
map-cong U          ip i x          = refl
map-cong (I i′)     ip i x          = ip i′ x
map-cong (X h F)    ip i x          = map-cong F ip (h i) x
map-cong (Y h F)    ip i x          = map-cong F (ip ∘ h) i x
map-cong (F ⊕ G)    ip i (inl x)    = cong≡ inl (map-cong F ip i x)
map-cong (F ⊕ G)    ip i (inr x)    = cong≡ inr (map-cong G ip i x)
map-cong (F ⊗ G)    ip i (x , y)    = cong≡₂ _,_ (map-cong F ip i x) (map-cong G ip i y)
map-cong (F ⊚ G)    ip i x          = map-cong F (map-cong G ip) i x
map-cong (! o′)     ip i x          = refl
map-cong (Σ g)      ip i (some x)   = cong≡ some (map-cong (g _) ip i x)
map-cong (Fix F)    ip i ⟨ x ⟩      = cong≡ ⟨_⟩ (map-cong F (∥-cong ip (map-cong (Fix F) ip)) i x)
map-cong {r = r} {s = s} (EP C D e) ip i x 
  = cong≡ (_≃_.to (e s i)) (map-cong C ip i (_≃_.from (e r i) x))

map-id : {I O : Set}{r : Indexed I}(C : Code I O) →
         map {r = r} C id⇉ ≗ id⇉
map-id Z          i ()
map-id U          i x               = refl
map-id (I i′)     i x               = refl
map-id (X h F)    i x               = map-id F (h i) x
map-id (Y h F)    i x               = map-id F i x
map-id (F ⊕ G)    i (inl x)         = cong≡ inl (map-id F i x)
map-id (F ⊕ G)    i (inr x)         = cong≡ inr (map-id G i x)
map-id (F ⊗ G)    i (x , y)         = cong≡₂ _,_ (map-id F i x) (map-id G i y)
map-id (F ⊚ G)    i x               = trans≡ (map-cong F (map-id G) i x) (map-id F i x)
map-id (! o′)     i x               = refl
map-id (Σ g)      i (some x)        = cong≡ some (map-id (g _) i x)
map-id (Fix F)    i ⟨ x ⟩           = cong≡ ⟨_⟩ (trans≡ (map-cong F (∥-id (λ _ _ → refl)
                                                                    (map-id (Fix F))) i x)
                                                        (map-id F i x))
map-id {r = r} (EP C D e) i x = sym≡ (trans≡ (sym≡ (_≃_.iso₁ (e r i))) 
                                 (sym≡ (cong≡ (_≃_.to (e r i)) 
                                              (map-id C i (_≃_.from (e r i) x)))))

-- The second proof proceeds in the same way
map-∘ : {I O : Set} {r s t : Indexed I}
        (C : Code I O)(f : s ⇉ t)(g : r ⇉ s)
      → map C (f ⇉∘ g) ≗ map C f ⇉∘ map C g
map-∘ Z          f g i ()
map-∘ U          f g i x            = refl
map-∘ (I i′)     f g i x            = refl
map-∘ (X h F)    f g i x            = map-∘ F f g (h i) x
map-∘ (Y h F)    f g i x            = map-∘ F (f ∘ h) (g ∘ h) i x
map-∘ (F ⊕ G)    f g i (inl x)      = cong≡ inl (map-∘ F f g i x)
map-∘ (F ⊕ G)    f g i (inr x)      = cong≡ inr (map-∘ G f g i x)
map-∘ (F ⊗ G)    f g i (x , y)      = cong≡₂ _,_ (map-∘ F f g i x) (map-∘ G f g i y)
map-∘ (F ⊚ G)    f g i x            = trans≡ (map-cong F (map-∘ G f g) i x)
                                             (map-∘ F (map G f) (map G g) i x)
map-∘ (! o′)     f g i x            = refl
map-∘ (Σ h)      f g i (some x)     = cong≡ some (map-∘ (h _) f g i x)
map-∘ (Fix F)    f g i ⟨ x ⟩        = cong≡ ⟨_⟩ (trans≡ (map-cong F (∥-cong (λ _ _ → refl)
                                                                            (map-∘ (Fix F) f g))
                                                                  i x)
                                                (trans≡ (map-cong F ∥-∘ i x)
                                                        (map-∘ F (f ∥ map (Fix F) f)
                                                                 (g ∥ map (Fix F) g) i x)))

map-∘ {r = r} {s = s} {t = t} (EP C D e) f g i x
  = {! (cong≡ (_≃_.to (e t i)) (map-∘ C f g i (_≃_.from (e r i) x))) !}
  -- need to use (sym≡ (_≃_.iso₂ (e r i)))

----------------------------------------------------------------------
-- Recursion patterns
----------------------------------------------------------------------

cata : {I O : Set} {r : Indexed I} {s : Indexed O} → (C : Code (I + O) O) →
       (⟦ C ⟧ (r ∣ s) ⇉ s) → ⟦ Fix C ⟧ r ⇉ s
cata C φ o ⟨ x ⟩ = φ o (map C (id⇉ ∥ cata C φ) o x)

ana : {I O : Set} {r : I → Set} {s : O → Set} → (C : Code (I + O) O) →
      (s ⇉ ⟦ C ⟧ (r ∣ s)) → s ⇉ ⟦ Fix C ⟧ r
ana C ψ o x = ⟨ map C (id⇉ ∥ ana C ψ) o (ψ o x) ⟩

hylo : {I O : Set} {r : I → Set} {s t : O → Set} → (C : Code (I + O) O) →
       (⟦ C ⟧ (r ∣ t) ⇉ t) → (s ⇉ ⟦ C ⟧ (r ∣ s)) → s ⇉ t
hylo C φ ψ o x = φ o (map C (id⇉ ∥ hylo C φ ψ) o (ψ o x))

para : {I O : Set} {r : I → Set} {s : O → Set} → (C : Code (I + O) O) →
       (⟦ C ⟧ (r ∣ λ o → s o × ⟦ Fix C ⟧ r o) ⇉ s) → ⟦ Fix C ⟧ r ⇉ s
para C φ o ⟨ x ⟩ = φ o (map C (id⇉ ∥ (λ i → (para C φ i) ▵ id)) o x)

apo : {I O : Set} {r : I → Set} {s : O → Set} → (C : Code (I + O) O) →
       (s ⇉ ⟦ C ⟧ (r ∣ λ o → s o + ⟦ Fix C ⟧ r o)) → s ⇉ ⟦ Fix C ⟧ r
apo C ψ o x = ⟨ map C (id⇉ ∥ (λ i → (apo C ψ i) ▿ id)) o (ψ o x) ⟩
