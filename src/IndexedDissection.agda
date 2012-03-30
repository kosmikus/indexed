module IndexedDissection where

open import Prelude

-- Indexed sets

Indexed : Set → Set₁
Indexed A = A → Set

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

-- Indexed functors
_▷_ : Set → Set → Set₁
I ▷ O = Indexed I → Indexed O

-- Functors

data Code : Set → Set → Set₁ where
  K    : {I O : Set}   → (A : Set) → Code I O
  Id   : {I : Set}     → Code I I
  _⊕_  : {I O : Set}   → (C D : Code I O) → Code I O
  _⊗_  : {I O : Set}   → (C D : Code I O) → Code I O
  AC   : {I J O : Set} → (C : Code I O) → Code (I + J) O  -- all clowns
  AJ   : {I J O : Set} → (C : Code I O) → Code (J + I) O  -- all jokers

-- I decide to include AC and AJ among the code, as we probably
-- want/need Fst and Snd among the codes, in order to have any chance
-- to recurse on a parameter or recursive position selectively.

Fst : {I O : Set} → Code (O + I) O
Fst = AC Id

Snd : {I O : Set} → Code (I + O) O
Snd = AJ Id

One : {I O : Set} → Code I O
One = K ⊤

Zero : {I O : Set} → Code I O
Zero = K ⊥

⟦_⟧ : {I O : Set} → Code I O → I ▷ O
⟦ K A ⟧    X o = A
⟦ Id ⟧     X o = X o
⟦ C ⊕ D ⟧  X o = ⟦ C ⟧ X o + ⟦ D ⟧ X o
⟦ C ⊗ D ⟧  X o = ⟦ C ⟧ X o × ⟦ D ⟧ X o
⟦ AC C ⟧   X o = ⟦ C ⟧ (X ∘ inl) o
⟦ AJ C ⟧   X o = ⟦ C ⟧ (X ∘ inr) o

fmap : {I O : Set} → (C : Code I O) → {A B : Indexed I} → (A ⇉ B) → ⟦ C ⟧ A ⇉ ⟦ C ⟧ B
fmap (K A)    f o x       = x
fmap Id       f o x       = f o x
fmap (C ⊕ D)  f o (inl x) = inl (fmap C f o x)
fmap (C ⊕ D)  f o (inr x) = inr (fmap D f o x)
fmap (C ⊗ D)  f o (x , y) = fmap C f o x , fmap D f o y
fmap (AC C)   f o x       = fmap C (f ∘ inl) o x
fmap (AJ C)   f o x       = fmap C (f ∘ inr) o x

data μ {I O : Set} (C : Code (I + O) O) (X : Indexed I) (o : O) : Set where
  ⟨_⟩ : (x : ⟦ C ⟧ (X ∣ μ C X) o) → μ C X o

data μ₀ {O : Set} (C : Code O O) (o : O) : Set where
  ⟨_⟩ : (x : ⟦ C ⟧ (μ₀ C) o) → μ₀ C o

cata : {I O : Set} (C : Code (I + O) O) →
       {X : Indexed I} {R : Indexed O} →
       (⟦ C ⟧ (X ∣ R) ⇉ R) → μ C X ⇉ R
cata C φ o ⟨ x ⟩ = φ o (fmap C (id⇉ ∥ cata C φ) o x)

cata₀ : {O : Set} (C : Code O O) {R : Indexed O} →
        (⟦ C ⟧ R ⇉ R) → μ₀ C ⇉ R
cata₀ C φ o ⟨ x ⟩ = φ o (fmap C (cata₀ C φ) o x)

-- Dissection

-- TODO: Giving up on returning a code, for now

-- The extra (input) index indicates the type of the hole.
Dis : {I O : Set} → Code I O → I → (I + I) ▷ O
Dis (K A)    i       X o = ⟦ Zero ⟧ X o
Dis Id       i       X o = i ≡ o -- × ⟦ One  ⟧ X o
Dis (C ⊕ D)  i       X o = Dis C i X o + Dis D i X o
Dis (C ⊗ D)  i       X o = (Dis C i X o × ⟦ AJ D ⟧ X o) + (⟦ AC C ⟧ X o × Dis D i X o)
Dis (AC C)   (inl i) X o = Dis C i (X ∘ (inl +++ inl)) o
Dis (AC C)   (inr i) X o = ⟦ Zero ⟧ X o
Dis (AJ C)   (inl i) X o = ⟦ Zero ⟧ X o
Dis (AJ C)   (inr i) X o = Dis C i (X ∘ (inr +++ inr)) o

-- hole is an i-structure, outside is an o-structure
Diss : {I O : Set} → Code I O → Indexed I → Indexed I → I → O → Set
Diss C c j i o = Dis C i (c ∣ j) o

mindp⊕ : {I O : Set} →
         (C D : Code I O) →
         {c j : Indexed I} →
         {o : O} →
         (∃ λ i → j i × Diss C       c j i o) + ⟦ C     ⟧ c o →
         (∃ λ i → j i × Diss (C ⊕ D) c j i o) + ⟦ C ⊕ D ⟧ c o
mindp⊕ _ _ (inl (some (j , dx))) = inl (some (j , inl dx))
mindp⊕ _ _ (inr xc)              = inr (inl xc)

mindq⊕ : {I O : Set} →
         (C D : Code I O) →
         {c j : Indexed I} →
         {o : O} →
         (∃ λ i → j i × Diss D       c j i o) + ⟦     D ⟧ c o →
         (∃ λ i → j i × Diss (C ⊕ D) c j i o) + ⟦ C ⊕ D ⟧ c o
mindq⊕ _ _ (inl (some (j , dx))) = inl (some (j , inr dx))
mindq⊕ _ _ (inr xc)              = inr (inr xc)

mindAC : {I J O : Set} →
         (C : Code I O) →
         {c j : Indexed (I + J)} →
         {o : O} →
         (∃ λ i → (j ∘ inl) i × Diss C      (c ∘ inl) (j ∘ inl) i o) + ⟦ C    ⟧ (c ∘ inl) o →
         (∃ λ i → j         i × Diss (AC C)  c         j        i o) + ⟦ AC C ⟧  c        o
mindAC _ (inl (some (j , dx))) = inl (some (j , {!dx!}))
mindAC _ (inr xc) = inr xc

mindAJ : {I J O : Set} →
         (C : Code I O) →
         {c j : Indexed (J + I)} →
         {o : O} →
         (∃ λ i → (j ∘ inr) i × Diss C      (c ∘ inr) (j ∘ inr) i o) + ⟦ C    ⟧ (c ∘ inr) o →
         (∃ λ i → j         i × Diss (AJ C)  c         j        i o) + ⟦ AJ C ⟧  c        o
mindAJ _ (inl (some (j , dx))) = inl (some (j , {!dx!}))
mindAJ _ (inr xc) = inr xc


mutual
  mindq⊗ : {I O : Set} →
           (C D : Code I O) →
           {c j : Indexed I} →
           {o : O} →
           ⟦ C ⟧ c o → ∃ (λ i → j i × Diss      D  c j i o) + ⟦     D ⟧ c o →
                      ∃ (λ i → j i × Diss (C ⊗ D) c j i o) + ⟦ C ⊗ D ⟧ c o
  mindq⊗ C D xc (inl (some (j , dy))) = inl (some (j , inr (xc , dy)))
  mindq⊗ C D xc (inr yc)              = inr (xc , yc)

  mindp⊗ : {I O : Set} →
           (C D : Code I O) →
           {c j : Indexed I} →
           {o : O} →
           ∃ (λ i → j i × Diss C       c j i o) + ⟦ C     ⟧ c o → ⟦ D ⟧ j o →
           ∃ (λ i → j i × Diss (C ⊗ D) c j i o) + ⟦ C ⊗ D ⟧ c o
  mindp⊗ C D (inl (some (j , dx))) yj = inl (some (j , inl (dx , yj)))
  mindp⊗ C D (inr xc) yj              = mindq⊗ C D xc (right D (inl yj))




  right : {I O : Set} → (C : Code I O) → {c j : Indexed I} → {o : O} →
          ⟦ C ⟧ j o + (∃ λ i → Diss C c j i o × c i) →
          (∃ λ i → j i × Diss C c j i o) + ⟦ C ⟧ c o

  right (K A)       (inl a)                          = inr a
  right (K A)       (inr (some (() , c)))

  right Id          (inl j)                          = inl (some (j , refl))
  right Id          (inr (some (refl , c)))          = inr c

  right (C ⊕ D)     (inl (inl xj))                   = mindp⊕ C D (right C (inl xj))
  right (C ⊕ D)     (inl (inr xj))                   = mindq⊕ C D (right D (inl xj))
  right (C ⊕ D)     (inr (some (inl dx , c)))        = mindp⊕ C D (right C (inr (some (dx , c))))
  right (C ⊕ D)     (inr (some (inr dx , c)))        = mindq⊕ C D (right D (inr (some (dx , c))))

  right (C ⊗ D)     (inl (xj , yj))                  = mindp⊗ C D (right C (inl xj)) yj
  right (C ⊗ D)     (inr (some (inl (dx , yj) , c))) = mindp⊗ C D (right C (inr (some (dx , c)))) yj
  right (C ⊗ D)     (inr (some (inr (xc , dy) , c))) = mindq⊗ C D xc (right D (inr (some (dy , c))))

  right (AC C)      (inl x)                          = mindAC C (right C (inl x))
  right (AC C)      (inr (some {x = inl i} (dx , c)))= mindAC C (right C (inr (some ({!dx!} , c))))
  right (AC C)      (inr (some {x = inr i} (() , c)))

  right (AJ C)      (inl x)                          = mindAJ C (right C (inl x))
  right (AJ C)      (inr (some {x = inl i} (() , c)))
  right (AJ C)      (inr (some {x = inr i} (dx , c)))= mindAJ C (right C (inr (some ({!dx!} , c))))
  
tmap : {I O : Set} → (C : Code I O) → {A B : Indexed I} → (A ⇉ B) → ⟦ C ⟧ A ⇉ ⟦ C ⟧ B
tmap C {A = A} {B = B} f o x = continue (right C (inl x))
  where
    continue : (∃ λ i → A i × Diss C B A i o) + ⟦ C ⟧ B o → ⟦ C ⟧ B o
    continue (inl (some (a , dx))) = continue (right C (inr (some (dx , f _ a))))
    continue (inr xb)              = xb

-- Tail-recursive catamorphism

data Stack₀ {O : Set} (A : O → O → Set) : O → O → Set where
  []  : {i : O} → Stack₀ A i i
  _∷_ : {i m o : O} → A i m → Stack₀ A m o → Stack₀ A i o

mutual
  next : {O : Set} → (C : Code O O) → {R : Indexed O} → (⟦ C ⟧ R ⇉ R) → {m o : O} →
         (∃ λ i → μ₀ C i × Diss C R (μ₀ C) i m) + ⟦ C ⟧ R m → Stack₀ (Diss C R (μ₀ C)) m o → R o
  next C φ (inl (some (x , dx))) dxs = load   C φ x       (dx ∷ dxs)
  next C φ (inr v)               dxs = unload C φ (φ _ v)       dxs

  load : {O : Set} → (C : Code O O) → {R : Indexed O} → (⟦ C ⟧ R ⇉ R) → {i o : O} →
         μ₀ C i → Stack₀ (Diss C R (μ₀ C)) i o → R o
  load C φ ⟨ x ⟩ dxs = next C φ (right C (inl x)) dxs

  unload : {O : Set} → (C : Code O O) → {R : Indexed O} → (⟦ C ⟧ R ⇉ R) → {i o : O} →
           R i → Stack₀ (Diss C R (μ₀ C)) i o → R o
  unload C φ v []         = v
  unload C φ v (dx ∷ dxs) = next C φ (right C (inr (some (dx , v)))) dxs

  tcata : {O : Set} → (C : Code O O) → {R : Indexed O} → (⟦ C ⟧ R ⇉ R) → μ₀ C ⇉ R
  tcata C φ _ x = load C φ x []

-- Derivative

∂ : {I O : Set} → Code I O → (Indexed I → I → O → Set)
∂ C X = Diss C X X

plug : {I O : Set} (C : Code I O) {X : Indexed I} {i : I} {o : O} →
       X i → ∂ C X i o → ⟦ C ⟧ X o
plug (K A)                x ()
plug Id                   x refl           = x  -- scary once again
plug (C ⊕ D)              x (inl dx)       = inl (plug C x dx)
plug (C ⊕ D)              x (inr dx)       = inr (plug D x dx)
plug (C ⊗ D)              x (inl (dx , y)) = plug C x dx , y
plug (C ⊗ D)              y (inr (x , dy)) = x , plug D y dy
plug (AC C) {i = inl i}   x dx             = plug C x {!dx!}
plug (AC C) {i = inr i}   x ()
plug (AJ C) {i = inl i}   x ()
plug (AJ C) {i = inr i}   x dx             = plug C x {!dx!}
