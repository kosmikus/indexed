{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --no-positivity-check #-}

open import Prelude

module IxFun2 
    (IxCode : Set)
    (_∔_    : IxCode → IxCode → IxCode)
    (⟪_⟫    : IxCode → Set)
    (∔→+    : {A B : IxCode} → ⟪ A ∔ B ⟫ → ⟪ A ⟫ + ⟪ B ⟫)
--    (p      : {A B : IxCode} → ⟪ A ∔ B ⟫ ≡ (⟪ A ⟫ + ⟪ B ⟫))
--    (≡ix    : (I J : IxCode) → Maybe (I ≡ J))
--    (≡ix    : {I : IxCode} → (i j : ⟪ I ⟫) → Maybe (i ≡ j))
  where

----------------------------------------------------------------------
-- The universe of indexed functors
----------------------------------------------------------------------

{-
∔→+'    : {A B : IxCode} → ⟪ A ∔ B ⟫ → ⟪ A ⟫ + ⟪ B ⟫
∔→+' x = subst≡' p x
-}

-- Indexed family.
Indexed : IxCode → Set₁
Indexed I = ⟪ I ⟫ → Set

-- Natural transformations.
_⇉_ : ∀ {I} → Indexed I → Indexed I → Set
r ⇉ s = forall i → r i → s i

-- Identity natural transformation.
id⇉ : {I : IxCode} {r : Indexed I} → r ⇉ r
id⇉ i = id

-- Composing natural transformations
_⇉∘_ : {I : IxCode} {r s t : Indexed I} → s ⇉ t → r ⇉ s → r ⇉ t
(f ⇉∘ g) i x = f i (g i x)
{-
-- Special case of const.
T : Set → Indexed ⊤
T A tt = A

-- Lifting a function to a (unit-type-indexed) natural transformation.
↑ : ∀ {A B : Set} → (A → B) → (T A ⇉ T B)
↑ f tt x = f x
-}

-- Merging indexed families.
infixr 5 _∣_
_∣_ : {I J : IxCode} → Indexed I → Indexed J → Indexed (I ∔ J)
(r ∣ s) x with ∔→+  x
(r ∣ s) _ | inl i = r i
(r ∣ s) _ | inr i = s i

-- Merging natural transformations.
infixr 5 _∥_
_∥_ : {I J : IxCode} {r u : Indexed I} {s v : Indexed J} →
     (r ⇉ u) → (s ⇉ v) → ((r ∣ s) ⇉ (u ∣ v))
_∥_ f g x with ∔→+  x
_∥_ f g _ | (inl x) = f x
_∥_ f g _ | (inr y) = g y

-- Binary relations (move to prelude)
Rel : Set → Set → Set₁
Rel A B = A → B → Set

-- Indexed functors
_▷_ : IxCode → IxCode → Set₁
I ▷ O = Indexed I → Indexed O

-- Codes for indexed functors
infixr 3 _⊕_
infixr 4 _⊗_
infixr 5 _⊚_

infix 3 _≃_
data _≃_ (A B : Set) : Set where
  ep : (from : A → B) → (to : B → A) → A ≃ B

mutual
  data Code : IxCode → IxCode → Set₁ where
    Z   : ∀ {I O} → Code I O
    U   : ∀ {I O} → Code I O
--    K   : ∀ {I O C D e} → (U : Code C D) → (C : U) → Code I O
    I   : ∀ {I O} → (i : ⟪ I ⟫) → Code I O
    X   : ∀ {I O O′} → (R : Rel ⟪ O ⟫ ⟪ O′ ⟫) → (F : Code I O′) → Code I O
    Y   : ∀ {I I′ O} → (⟪ I′ ⟫ → ⟪ I ⟫) → (F : Code I′ O) → Code I O
    _⊕_ : ∀ {I O} → (F : Code I O) → (G : Code I O) → Code I O
    _⊗_ : ∀ {I O} → (F : Code I O) → (G : Code I O) → Code I O
    _⊚_ : ∀ {I M O} → (F : Code M O) → (G : Code I M) → Code I O
    !   : ∀ {I O} → (o′ : ⟪ O ⟫) → Code I O
    Σ  : ∀ {I O J K r o} {C : Code J K} → (⟦ C ⟧ r o → Code I O) → Code I O
    Fix : ∀ {I O} → (F : Code (I ∔ O) O) → Code I O
    EP  : ∀ {I O} → (C : Code I O) → (D : I ▷ O)
                  → (e : (r : Indexed I) → (o : ⟪ O ⟫) → D r o ≃ ⟦ C ⟧ r o)
                  → Code I O

-- Interpretation of codes as indexed functors.
  data μ {I O : IxCode} (F : Code (I ∔ O) O) (r : Indexed I) (o : ⟪ O ⟫) : Set where
    ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

  ⟦_⟧ : ∀ {I O : IxCode} → Code I O → I ▷ O
  ⟦ Z     ⟧    r o = ⊥
  ⟦ U     ⟧    r o = ⊤
--  ⟦ K C   ⟧    r o = ∀ s o′ → ⟦ C ⟧ s o′
  ⟦ I i   ⟧    r o = r i
  ⟦ X R F ⟧    r o = ∃ (λ o′ → R o o′ × ⟦ F ⟧ r o′)
  ⟦ Y f F ⟧    r o = ⟦ F ⟧ (r ∘ f) o
  ⟦ F ⊕ G ⟧    r o = ⟦ F ⟧ r o + ⟦ G ⟧ r o
  ⟦ F ⊗ G ⟧    r o = ⟦ F ⟧ r o × ⟦ G ⟧ r o
  ⟦ F ⊚ G ⟧    r o = ⟦ F ⟧ (⟦ G ⟧ r) o
  ⟦ ! o′  ⟧    r o = o ≡ o′
  ⟦ Σ f   ⟧    r o = ∃ (λ i → ⟦ f i ⟧ r o)
  ⟦ Fix F ⟧    r o = μ F r o
  ⟦ EP C D e ⟧ r o = D r o


----------------------------------------------------------------------
-- Definition of map for indexed functors
----------------------------------------------------------------------

map : {I O : IxCode} {r s : Indexed I} (C : Code I O) →
      (r ⇉ s) → (⟦ C ⟧ r ⇉ ⟦ C ⟧ s)
map Z          f o ()
map U          f o x                   = x
--map (K C)      f o x                   = x
map (I i)      f o x                   = f i x
map (X R F)    f o (some {o′} (p , x)) = some (p , map F f o′ x)
map (Y g F)    f o x                   = map F (λ i → f (g i)) o x
map (F ⊕ G)    f o (inl x)             = inl (map F f o x)
map (F ⊕ G)    f o (inr y)             = inr (map G f o y)
map (F ⊗ G)    f o (x , y)             = map F f o x , map G f o y
map (F ⊚ G)    f o x                   = map F (map G f) o x
map (! o')     f o x                   = x
map (Σ g)      f o (some {i} x)        = some (map (g i) f o x)
map (Fix F)    f o ⟨ x ⟩               = ⟨ map F (f ∥ map (Fix F) f) o x ⟩

map {r = r} {s = s} (EP C D e) f o x with (e r o , e s o)
map (EP C _ _) f o x | (ep from _ , ep _ to) = to (map C f o (from x))

----------------------------------------------------------------------
-- Recursion patterns
----------------------------------------------------------------------

cata : {I O : IxCode} {r : Indexed I} {s : Indexed O} → (C : Code (I ∔ O) O) →
       (⟦ C ⟧ (r ∣ s) ⇉ s) → ⟦ Fix C ⟧ r ⇉ s
cata C φ o ⟨ x ⟩ = φ o (map C (id⇉ ∥ cata C φ) o x)

ana : {I O : IxCode} {r : Indexed I} {s : Indexed O} → (C : Code (I ∔ O) O) →
      (s ⇉ ⟦ C ⟧ (r ∣ s)) → s ⇉ ⟦ Fix C ⟧ r
ana C ψ o x = ⟨ map C (id⇉ ∥ ana C ψ) o (ψ o x) ⟩

hylo : {I O : IxCode} {r : Indexed I} {s t : Indexed O} → (C : Code (I ∔ O) O) →
       (⟦ C ⟧ (r ∣ t) ⇉ t) → (s ⇉ ⟦ C ⟧ (r ∣ s)) → s ⇉ t
hylo C φ ψ o x = φ o (map C (id⇉ ∥ hylo C φ ψ) o (ψ o x))

para : {I O : IxCode} {r : Indexed I} {s : Indexed O} → (C : Code (I ∔ O) O) →
       (⟦ C ⟧ (r ∣ λ o → s o × ⟦ Fix C ⟧ r o) ⇉ s) → ⟦ Fix C ⟧ r ⇉ s
para C φ o ⟨ x ⟩ = φ o (map C (id⇉ ∥ (λ i → (para C φ i) ▵ id)) o x)

apo : {I O : IxCode} {r : Indexed I} {s : Indexed O} → (C : Code (I ∔ O) O) →
       (s ⇉ ⟦ C ⟧ (r ∣ λ o → s o + ⟦ Fix C ⟧ r o)) → s ⇉ ⟦ Fix C ⟧ r
apo C ψ o x = ⟨ map C (id⇉ ∥ (λ i → (apo C ψ i) ▿ id)) o (ψ o x) ⟩
