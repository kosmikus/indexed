{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}
module IxFun where

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

-- The proofs are optional
infix 3 _≃_
record _≃_ (A B : Set) : Set where
  field
    from  : A → B
    to    : B → A
    iso₁  : ∀ {x} → Maybe (to (from x) ≡ x)
    iso₂  : ∀ {x} → Maybe (from (to x) ≡ x)


mutual
  data Code : Set → Set → Set₁ where
    Z   : ∀ {I O} → Code I O
    U   : ∀ {I O} → Code I O
--    K   : ∀ {I O C D e} → (U : Code C D) → (C : U) → Code I O
    I   : ∀ {I O} → (i : I) → Code I O
--    X   : ∀ {I O O′} → (R : Rel O O′) → (F : Code I O′) → Code I O
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
--  ⟦ K C   ⟧    r o = ∀ s o′ → ⟦ C ⟧ s o′
  ⟦ I i   ⟧    r o = r i
  ⟦ X f F ⟧    r o = ⟦ F ⟧ r (f o) -- ∃ (λ o′ → R o o′ × ⟦ F ⟧ r o′)
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
--map (K C)      f o x                   = x
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

map {r = r} {s = s} (EP C D e) f o x with (e r o , e s o)
map (EP C _ _) f o x | (ep₁ , ep₂) = _≃_.to ep₂ (map C f o (_≃_.from ep₁ x))


-- Applicative version of map
record Applicative (F : Set → Set) : Set₁ where
  infixl 4 _⊛_
  field
    pure : ∀ {A} → A → F A
    _⊛_  : ∀ {A B} → F (A → B) → F A → F B

module tmap {a : Set → Set} (A : Applicative a) where
  open Applicative A

  _⇉a_ : ∀ {I} → Indexed I → Indexed I → Set
  r ⇉a s = forall i → r i → a (s i)

  infixr 5 _∥a_
  _∥a_ : ∀ {I J} {r u : Indexed I} {s v : Indexed J}
       → r ⇉a u → s ⇉a v → (r ∣ s) ⇉a (u ∣ v)
  _∥a_ f g (inl x) = f x
  _∥a_ f g (inr x) = g x

  -- _∮_ == _<$>_
  infixl 4 _∮_
  _∮_ : {A B : Set} → (A → B) → a A → a B
  f ∮ x = pure f ⊛ x

  tmap : {I O : Set} {r s : Indexed I} → (C : Code I O)
       → (r ⇉a s) → (⟦ C ⟧ r ⇉a ⟦ C ⟧ s)
  tmap Z       f o x            = pure x
  tmap U       f o x            = pure x
  tmap (I i)   f o x            = f i x
  tmap (X g F) f o x            = tmap F f (g o) x
  tmap (Y y F) f o x            = tmap F (f ∘ y) o x
  tmap (F ⊕ G) f o (inl y)      = inl ∮ tmap F f o y
  tmap (F ⊕ G) f o (inr y)      = inr ∮ tmap G f o y
  tmap (F ⊗ G) f o (x , y)      = _,_ ∮ tmap F f o x ⊛ tmap G f o y
  tmap (F ⊚ G) f o x            = tmap F (tmap G f) o x
  tmap (! o′)  f o x            = pure x
  tmap (Σ g)   f o (some {i} x) = some ∮ tmap (g i) f o x
  tmap (Fix F) f o ⟨ x ⟩        = ⟨_⟩ ∮ tmap F (f ∥a tmap (Fix F) f) o x

  tmap {r = r} {s = s} (EP C D e) f o x with (e r o , e s o)
  tmap (EP C _ _) f o x | (ep₁ , ep₂) = (_≃_.to ep₂) ∮ tmap C f o (_≃_.from ep₁ x)

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
