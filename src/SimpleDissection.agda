module SimpleDissection where

open import Prelude

-- Functors

data Code₁ : Set₁ where
  K₁ : (A : Set) → Code₁
  Id : Code₁
  _⊕₁_ : (C D : Code₁) → Code₁
  _⊗₁_ : (C D : Code₁) → Code₁

⟦_⟧₁ : Code₁ → (Set → Set)
⟦ K₁ A ⟧₁   X = A
⟦ Id ⟧₁     X = X
⟦ C ⊕₁ D ⟧₁ X = ⟦ C ⟧₁ X + ⟦ D ⟧₁ X
⟦ C ⊗₁ D ⟧₁ X = ⟦ C ⟧₁ X × ⟦ D ⟧₁ X

fmap : (C : Code₁) → {A B : Set} → (A → B) → ⟦ C ⟧₁ A → ⟦ C ⟧₁ B
fmap (K₁ A)   f x       = x
fmap Id       f x       = f x
fmap (C ⊕₁ D) f (inl x) = inl (fmap C f x)
fmap (C ⊕₁ D) f (inr x) = inr (fmap D f x)
fmap (C ⊗₁ D) f (x , y) = fmap C f x , fmap D f y

data μ (C : Code₁) : Set where
  ⟨_⟩₁ : (x : ⟦ C ⟧₁ (μ C)) → μ C

cata : (C : Code₁) → {R : Set} → (⟦ C ⟧₁ R → R) → μ C → R
cata C φ ⟨ x ⟩₁ = φ (fmap C (cata C φ) x)

-- Bifunctors

data Code₂ : Set₁ where
  K₂   : (A : Set) → Code₂
  Fst  : Code₂
  Snd  : Code₂
  _⊕₂_ : (C D : Code₂) → Code₂
  _⊗₂_ : (C D : Code₂) → Code₂
  AC   : (C : Code₁) → Code₂  -- all clowns
  AJ   : (C : Code₁) → Code₂  -- all jokers

⟦_⟧₂ : Code₂ → (Set → Set → Set)
⟦ K₂ A ⟧₂   X Y = A
⟦ Fst ⟧₂    X Y = X
⟦ Snd ⟧₂    X Y = Y
⟦ C ⊕₂ D ⟧₂ X Y = ⟦ C ⟧₂ X Y + ⟦ D ⟧₂ X Y
⟦ C ⊗₂ D ⟧₂ X Y = ⟦ C ⟧₂ X Y × ⟦ D ⟧₂ X Y
⟦ AC C ⟧₂   X Y = ⟦ C ⟧₁ X
⟦ AJ C ⟧₂   X Y = ⟦ C ⟧₁ Y

1₂ : Code₂
1₂ = K₂ ⊤

bimap : (C : Code₂) → {A₁ A₂ B₁ B₂ : Set} →
        (A₁ → B₁) → (A₂ → B₂) →
        ⟦ C ⟧₂ A₁ A₂ → ⟦ C ⟧₂ B₁ B₂
bimap (K₂ A)   f g x       = x
bimap Fst      f g x       = f x
bimap Snd      f g x       = g x
bimap (C ⊕₂ D) f g (inl x) = inl (bimap C f g x)
bimap (C ⊕₂ D) f g (inr x) = inr (bimap D f g x)
bimap (C ⊗₂ D) f g (x , y) = bimap C f g x , bimap D f g y
bimap (AC C)   f g x       = fmap C f x
bimap (AJ C)   f g x       = fmap C g x

0₁ : Code₁
0₁ = K₁ ⊥

0₂ : Code₂
0₂ = K₂ ⊥

-- Dissection

Dis : Code₁ → Code₂
Dis (K₁ A)   = 0₂
Dis Id       = 1₂
Dis (C ⊕₁ D) = Dis C ⊕₂ Dis D
Dis (C ⊗₁ D) = (Dis C ⊗₂ AJ D) ⊕₂ (AC C ⊗₂ Dis D)

mindp⊕ : (C D : Code₁) →
         {c j : Set} →
         j ×  ⟦ Dis  C       ⟧₂ c j  + ⟦ C      ⟧₁ c →
         j × (⟦ Dis (C ⊕₁ D) ⟧₂ c j) + ⟦ C ⊕₁ D ⟧₁ c
mindp⊕ _ _ (inl (j , dx)) = inl (j , inl dx)
mindp⊕ _ _ (inr xc)       = inr (inl xc)

mindq⊕ : (C D : Code₁) →
         {c j : Set} →
         j ×  ⟦ Dis       D  ⟧₂ c j  + ⟦      D ⟧₁ c →
         j × (⟦ Dis (C ⊕₁ D) ⟧₂ c j) + ⟦ C ⊕₁ D ⟧₁ c
mindq⊕ _ _ (inl (j , dx)) = inl (j , inr dx)
mindq⊕ _ _ (inr xc)       = inr (inr xc)

mutual
  mindq⊗ : (C D : Code₁) →
           {c j : Set} →
           ⟦ C ⟧₁ c → j × ⟦ Dis       D  ⟧₂ c j + ⟦      D ⟧₁ c →
                     j × ⟦ Dis (C ⊗₁ D) ⟧₂ c j + ⟦ C ⊗₁ D ⟧₁ c
  mindq⊗ C D xc (inl (j , dy)) = inl (j , inr (xc , dy))
  mindq⊗ C D xc (inr yc)       = inr (xc , yc)

  mindp⊗ : (C D : Code₁) →
           {c j : Set} →
           j × ⟦ Dis C        ⟧₂ c j + ⟦ C      ⟧₁ c → ⟦ D ⟧₁ j →
           j × ⟦ Dis (C ⊗₁ D) ⟧₂ c j + ⟦ C ⊗₁ D ⟧₁ c
  mindp⊗ C D (inl (j , dx)) yj = inl (j , inl (dx , yj))
  mindp⊗ C D (inr xc) yj       = mindq⊗ C D xc (right D (inl yj))

  right : (C : Code₁) → {c j : Set} →
          ⟦ C ⟧₁ j + (⟦ Dis C ⟧₂ c j × c) →
          (j × ⟦ Dis C ⟧₂ c j) + ⟦ C ⟧₁ c

  right (K₁ A)   (inl a)                   = inr a
  right (K₁ A)   (inr (() , c))

  right Id       (inl j)                   = inl (j , tt)
  right Id       (inr (tt , c))            = inr c

  right (C ⊕₁ D) (inl (inl xj))            = mindp⊕ C D (right C (inl xj))
  right (C ⊕₁ D) (inl (inr xj))            = mindq⊕ C D (right D (inl xj))
  right (C ⊕₁ D) (inr (inl dx , c))        = mindp⊕ C D (right C (inr (dx , c)))
  right (C ⊕₁ D) (inr (inr dx , c))        = mindq⊕ C D (right D (inr (dx , c)))

  right (C ⊗₁ D) (inl (xj , yj))           = mindp⊗ C D (right C (inl xj)) yj
  right (C ⊗₁ D) (inr (inl (dx , yj) , c)) = mindp⊗ C D (right C (inr (dx , c))) yj
  right (C ⊗₁ D) (inr (inr (xc , dy) , c)) = mindq⊗ C D xc (right D (inr (dy , c)))

tmap : (C : Code₁) → {A B : Set} → (A → B) → ⟦ C ⟧₁ A → ⟦ C ⟧₁ B
tmap C {A = A} {B = B} f x = continue (right C (inl x))
  where
    continue : A × ⟦ Dis C ⟧₂ B A + ⟦ C ⟧₁ B → ⟦ C ⟧₁ B
    continue (inl (a , dx)) = continue (right C (inr (dx , f a)))
    continue (inr xb)       = xb

-- Tail-recursive catamorphism

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

mutual
  next : (C : Code₁) → {R : Set} → (⟦ C ⟧₁ R → R) →
         (μ C × ⟦ Dis C ⟧₂ R (μ C)) + ⟦ C ⟧₁ R → List (⟦ Dis C ⟧₂ R (μ C)) → R
  next C φ (inl (x , dx)) dxs = load   C φ x     (dx ∷ dxs)
  next C φ (inr v)        dxs = unload C φ (φ v)       dxs

  load : (C : Code₁) → {R : Set} → (⟦ C ⟧₁ R → R) →
         μ C → List (⟦ Dis C ⟧₂ R (μ C)) → R
  load C φ ⟨ x ⟩₁ dxs = next C φ (right C (inl x)) dxs

  unload : (C : Code₁) → {R : Set} → (⟦ C ⟧₁ R → R) →
           R → List (⟦ Dis C ⟧₂ R (μ C)) → R
  unload C φ v []         = v
  unload C φ v (dx ∷ dxs) = next C φ (right C (inr (dx , v))) dxs

  tcata : (C : Code₁) → {R : Set} → (⟦ C ⟧₁ R → R) → μ C → R
  tcata C φ x = load C φ x []

-- Derivative

∂ : Code₁ → (Set → Set)
∂ C X = ⟦ Dis C ⟧₂ X X

plug : (C : Code₁) → {X : Set} → X → ∂ C X → ⟦ C ⟧₁ X
plug (K₁ A)   x ()
plug Id       x tt             = x
plug (C ⊕₁ D) x (inl dx)       = inl (plug C x dx)
plug (C ⊕₁ D) x (inr dx)       = inr (plug D x dx)
plug (C ⊗₁ D) x (inl (dx , y)) = plug C x dx , y
plug (C ⊗₁ D) y (inr (x , dy)) = x , plug D y dy