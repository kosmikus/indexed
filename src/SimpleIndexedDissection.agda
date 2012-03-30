module SimpleIndexedDissection where

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

data Code₁ : Set₁ where
  K₁ : (A : Set) → Code₁
  Id : Code₁
  _⊕₁_ : (C D : Code₁) → Code₁
  _⊗₁_ : (C D : Code₁) → Code₁

⟦_⟧₁ : Code₁ → (Indexed ⊤ → Indexed ⊤)
⟦ K₁ A ⟧₁   X o = A
⟦ Id ⟧₁     X o = X o
⟦ C ⊕₁ D ⟧₁ X o = ⟦ C ⟧₁ X o + ⟦ D ⟧₁ X o
⟦ C ⊗₁ D ⟧₁ X o = ⟦ C ⟧₁ X o × ⟦ D ⟧₁ X o

fmap : (C : Code₁) → {A B : Indexed ⊤} → (A ⇉ B) → ⟦ C ⟧₁ A ⇉ ⟦ C ⟧₁ B
fmap (K₁ A)   f o x       = x
fmap Id       f o x       = f o x
fmap (C ⊕₁ D) f o (inl x) = inl (fmap C f o x)
fmap (C ⊕₁ D) f o (inr x) = inr (fmap D f o x)
fmap (C ⊗₁ D) f o (x , y) = fmap C f o x , fmap D f o y

data μ (C : Code₁) : Indexed ⊤ where
  ⟨_⟩₁ : {i : ⊤} → (x : ⟦ C ⟧₁ (μ C) i) → μ C i -- might be wrong

cata : (C : Code₁) → {R : Indexed ⊤} → (⟦ C ⟧₁ R ⇉ R) → μ C ⇉ R
cata C φ o ⟨ x ⟩₁ = φ o (fmap C (cata C φ) o x)

-- Bifunctors

data Code₂ : Set₁ where
  K₂   : (A : Set) → Code₂
  Fst  : Code₂
  Snd  : Code₂
  _⊕₂_ : (C D : Code₂) → Code₂
  _⊗₂_ : (C D : Code₂) → Code₂
  AC   : (C : Code₁) → Code₂  -- all clowns
  AJ   : (C : Code₁) → Code₂  -- all jokers

⟦_⟧₂ : Code₂ → (Indexed (⊤ + ⊤) → Indexed ⊤)
⟦ K₂ A ⟧₂   X o = A
⟦ Fst ⟧₂    X o = X (inl o)
⟦ Snd ⟧₂    X o = X (inr o)
⟦ C ⊕₂ D ⟧₂ X o = ⟦ C ⟧₂ X o + ⟦ D ⟧₂ X o
⟦ C ⊗₂ D ⟧₂ X o = ⟦ C ⟧₂ X o × ⟦ D ⟧₂ X o
⟦ AC C ⟧₂   X o = ⟦ C ⟧₁ (X ∘ inl) o
⟦ AJ C ⟧₂   X o = ⟦ C ⟧₁ (X ∘ inr) o

1₂ : Code₂
1₂ = K₂ ⊤

bimap : (C : Code₂) → {A B : Indexed (⊤ + ⊤)} →
        (A ⇉ B) → ⟦ C ⟧₂ A ⇉ ⟦ C ⟧₂ B
bimap (K₂ A)   f o x       = x
bimap Fst      f o x       = f (inl o) x
bimap Snd      f o x       = f (inr o) x
bimap (C ⊕₂ D) f o (inl x) = inl (bimap C f o x)
bimap (C ⊕₂ D) f o (inr x) = inr (bimap D f o x)
bimap (C ⊗₂ D) f o (x , y) = bimap C f o x , bimap D f o y
bimap (AC C)   f o x       = fmap C (f ∘ inl) o x
bimap (AJ C)   f o x       = fmap C (f ∘ inr) o x

0₁ : Code₁
0₁ = K₁ ⊥

0₂ : Code₂
0₂ = K₂ ⊥

-- Dissection

-- The extra (input) index indicates the type of the hole.
Dis : Code₁ → ⊤ → Code₂
Dis (K₁ A)   i = 0₂
Dis Id       i = 1₂
Dis (C ⊕₁ D) i = Dis C i ⊕₂ Dis D i
Dis (C ⊗₁ D) i = (Dis C i ⊗₂ AJ D) ⊕₂ (AC C ⊗₂ Dis D i)

-- hole is an i-structure, outside is an o-structure
Diss : Code₁ → Indexed ⊤ → Indexed ⊤ → ⊤ → ⊤ → Set
Diss C c j i o = ⟦ Dis C i ⟧₂ (c ∣ j) o

mindp⊕ : (C D : Code₁) →
         {c j : Indexed ⊤} →
         {o : ⊤} →
         (∃ λ i → j i × Diss C        c j i o) + ⟦ C      ⟧₁ c o →
         (∃ λ i → j i × Diss (C ⊕₁ D) c j i o) + ⟦ C ⊕₁ D ⟧₁ c o
mindp⊕ _ _ (inl (some (j , dx))) = inl (some (j , inl dx))
mindp⊕ _ _ (inr xc)              = inr (inl xc)

mindq⊕ : (C D : Code₁) →
         {c j : Indexed ⊤} →
         {o : ⊤} →
         (∃ λ i → j i × Diss D        c j i o) + ⟦      D ⟧₁ c o →
         (∃ λ i → j i × Diss (C ⊕₁ D) c j i o) + ⟦ C ⊕₁ D ⟧₁ c o
mindq⊕ _ _ (inl (some (j , dx))) = inl (some (j , inr dx))
mindq⊕ _ _ (inr xc)              = inr (inr xc)

mutual
  mindq⊗ : (C D : Code₁) →
           {c j : Indexed ⊤} →
           {o : ⊤} →
           ⟦ C ⟧₁ c o → ∃ (λ i → j i × Diss       D  c j i o) + ⟦      D ⟧₁ c o →
                       ∃ (λ i → j i × Diss (C ⊗₁ D) c j i o) + ⟦ C ⊗₁ D ⟧₁ c o
  mindq⊗ C D xc (inl (some (j , dy))) = inl (some (j , inr (xc , dy)))
  mindq⊗ C D xc (inr yc)              = inr (xc , yc)

  mindp⊗ : (C D : Code₁) →
           {c j : Indexed ⊤} →
           {o : ⊤} →
           ∃ (λ i → j i × Diss C        c j i o) + ⟦ C      ⟧₁ c o → ⟦ D ⟧₁ j o →
           ∃ (λ i → j i × Diss (C ⊗₁ D) c j i o) + ⟦ C ⊗₁ D ⟧₁ c o
  mindp⊗ C D (inl (some (j , dx))) yj = inl (some (j , inl (dx , yj)))
  mindp⊗ C D (inr xc) yj              = mindq⊗ C D xc (right D (inl yj))

  right : (C : Code₁) → {c j : Indexed ⊤} → {o : ⊤} →
          ⟦ C ⟧₁ j o + (∃ λ i → Diss C c j i o × c i) →
          (∃ λ i → j i × Diss C c j i o) + ⟦ C ⟧₁ c o

  right (K₁ A)      (inl a)                          = inr a
  right (K₁ A)      (inr (some (() , c)))

  right Id          (inl j)                          = inl (some (j , tt))
  right Id {o = tt} (inr (some {x = tt} (tt , c)))   = inr c
    -- a bit uncertain; the type should enforce the index equality

  right (C ⊕₁ D)    (inl (inl xj))                   = mindp⊕ C D (right C (inl xj))
  right (C ⊕₁ D)    (inl (inr xj))                   = mindq⊕ C D (right D (inl xj))
  right (C ⊕₁ D)    (inr (some (inl dx , c)))        = mindp⊕ C D (right C (inr (some (dx , c))))
  right (C ⊕₁ D)    (inr (some (inr dx , c)))        = mindq⊕ C D (right D (inr (some (dx , c))))

  right (C ⊗₁ D)    (inl (xj , yj))                  = mindp⊗ C D (right C (inl xj)) yj
  right (C ⊗₁ D)    (inr (some (inl (dx , yj) , c))) = mindp⊗ C D (right C (inr (some (dx , c)))) yj
  right (C ⊗₁ D)    (inr (some (inr (xc , dy) , c))) = mindq⊗ C D xc (right D (inr (some (dy , c))))
  
tmap : (C : Code₁) → {A B : Indexed ⊤} → (A ⇉ B) → ⟦ C ⟧₁ A ⇉ ⟦ C ⟧₁ B
tmap C {A = A} {B = B} f o x = continue (right C (inl x))
  where
    continue : (∃ λ i → A i × Diss C B A i o) + ⟦ C ⟧₁ B o → ⟦ C ⟧₁ B o
    continue (inl (some (a , dx))) = continue (right C (inr (some (dx , f _ a))))
    continue (inr xb)              = xb

-- Tail-recursive catamorphism

data Stack (A : ⊤ → ⊤ → Set) : ⊤ → ⊤ → Set where
  []  : {i : ⊤} → Stack A i i
  _∷_ : {i m o : ⊤} → A i m → Stack A m o → Stack A i o

mutual
  next : (C : Code₁) → {R : Indexed ⊤} → (⟦ C ⟧₁ R ⇉ R) → {m o : ⊤} →
         (∃ λ i → μ C i × Diss C R (μ C) i m) + ⟦ C ⟧₁ R m → Stack (Diss C R (μ C)) m o → R o
  next C φ (inl (some (x , dx))) dxs = load   C φ x       (dx ∷ dxs)
  next C φ (inr v)               dxs = unload C φ (φ _ v)       dxs

  load : (C : Code₁) → {R : Indexed ⊤} → (⟦ C ⟧₁ R ⇉ R) → {i o : ⊤} →
         μ C i → Stack (Diss C R (μ C)) i o → R o
  load C φ ⟨ x ⟩₁ dxs = next C φ (right C (inl x)) dxs

  unload : (C : Code₁) → {R : Indexed ⊤} → (⟦ C ⟧₁ R ⇉ R) → {i o : ⊤} →
           R i → Stack (Diss C R (μ C)) i o → R o
  unload C φ v []         = v
  unload C φ v (dx ∷ dxs) = next C φ (right C (inr (some (dx , v)))) dxs

  tcata : (C : Code₁) → {R : Indexed ⊤} → (⟦ C ⟧₁ R ⇉ R) → μ C ⇉ R
  tcata C φ _ x = load C φ x []

-- Derivative

∂ : Code₁ → (Indexed ⊤ → ⊤ → ⊤ → Set)
∂ C X = Diss C X X

plug : (C : Code₁) → {X : Indexed ⊤} → {i o : ⊤} → X i → ∂ C X i o → ⟦ C ⟧₁ X o
plug (K₁ A)               x ()
plug Id {i = tt} {o = tt} x tt             = x  -- scary once again
plug (C ⊕₁ D)             x (inl dx)       = inl (plug C x dx)
plug (C ⊕₁ D)             x (inr dx)       = inr (plug D x dx)
plug (C ⊗₁ D)             x (inl (dx , y)) = plug C x dx , y
plug (C ⊗₁ D)             y (inr (x , dy)) = x , plug D y dy
