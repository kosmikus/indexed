{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type #-}

module PolyP where

  open import Prelude


  data Code : Set₁ where
    U   : Code
    I   : Code
    P   : Code
    K   : (X : Set) → Code
    _⊕_ : (F G : Code) → Code
    _⊗_ : (F G : Code) → Code
    _⊚_ : (F G : Code) → Code

  mutual
    ⟦_⟧ : Code → (Set → Set → Set)
    ⟦ U ⟧     A R = ⊤
    ⟦ I ⟧     A R = R
    ⟦ P ⟧     A R = A
    ⟦ K X ⟧   A R = X
    ⟦ F ⊕ G ⟧ A R = ⟦ F ⟧ A R ⊎ ⟦ G ⟧ A R
    ⟦ F ⊗ G ⟧ A R = ⟦ F ⟧ A R × ⟦ G ⟧ A R
    ⟦ F ⊚ G ⟧ A R = μ F (⟦ G ⟧ A R) -- first argument always interpreted as μ

    data μ (F : Code) (A : Set) : Set where
      ⟨_⟩ : ⟦ F ⟧ A (μ F A) → μ F A

  inn : ∀ {F A} → 
            ⟦ F ⟧ A (μ F A) ← μ F A
  inn ⟨ x ⟩ = x

  mutual
    map : (F : Code) → {A B R S : Set} → (A → B) → (R → S) → ⟦ F ⟧ A R → ⟦ F ⟧ B S
    map U f g _ = tt
    map I f g x = g x
    map P f g x = f x
    map (K X) f g x = x
    map (F ⊕ G) f g (inj₁ x) = inj₁ (map F f g x)
    map (F ⊕ G) f g (inj₂ y) = inj₂ (map G f g y)
    map (F ⊗ G) f g (x , y) = map F f g x , map G f g y
    map (F ⊚ G) f g ⟨ x ⟩ = ⟨ map F (map G f g) (map (F ⊚ G) f g) x ⟩

    -- The pmap corresponds to Haskell's fmap.
    pmap : {F : Code} {A B : Set} → (A → B) → μ F A → μ F B
    pmap {F} f ⟨ x ⟩ = ⟨ map F f (pmap {F} f) x ⟩

  cata : {F : Code} {A R : Set} → (⟦ F ⟧ A R → R) → (μ F A → R)
  cata {F} φ ⟨ x ⟩ = φ (map F id (cata φ) x)

  infix 4 _≅_
  _≅_ : ∀ {A B : Set} (f g : A → B) → Set
  f ≅ g = ∀ x → f x ≡ g x

  -- Trying some functions from the PolyP library. They can be converted
  -- more or less directly to this universe.
  open import Data.Nat

  mutual
    fsum : (F : Code) → ⟦ F ⟧ ℕ ℕ → ℕ
    fsum U x = 0
    fsum I x = x
    fsum P x = x
    fsum (K X) x = 0
    fsum (F ⊕ G) (inj₁ x) = fsum F x
    fsum (F ⊕ G) (inj₂ y) = fsum G y
    fsum (F ⊗ G) (x , y) = fsum F x + fsum G y
    fsum (F ⊚ G) x = psum (pmap (fsum G) x)

    psum : {F : Code} → μ F ℕ → ℕ
    psum {F} = cata (fsum F)

  open import Data.List hiding (map)

  mutual
    fflatten : (F : Code) {A : Set} → ⟦ F ⟧ (List A) (List A) → List A
    fflatten U x = []
    fflatten I x = x
    fflatten P x = x
    fflatten (K X) x = []
    fflatten (F ⊕ G) (inj₁ x) = fflatten F x
    fflatten (F ⊕ G) (inj₂ y) = fflatten G y
    fflatten (F ⊗ G) (x , y) = fflatten F x ++ fflatten G y
    fflatten (F ⊚ G) x = concat (flatten (pmap (fflatten G) x))

    flatten : {F : Code} {A : Set} → μ F A → List A
    flatten {F} ⟨ x ⟩ = fflatten F (map F [_] flatten x)

  -- Testing some encodings
  -- Lists
  ListC : Code
  ListC = U ⊕ (P ⊗ I)

  nil : {A : Set} → μ ListC A
  nil = ⟨ inj₁ tt ⟩

  cons : {A : Set} → A → μ ListC A → μ ListC A
  cons x xs = ⟨ inj₂ (x , xs) ⟩

  aList : μ ListC ℕ
  aList = cons 0 (cons 1 nil)

  -- Leaf trees
  TreeC : Code
  TreeC = P ⊕ (I ⊗ I)

  leaf : {A : Set} → A → μ TreeC A
  leaf x = ⟨ inj₁ x ⟩

  node : {A : Set} → μ TreeC A → μ TreeC A → μ TreeC A
  node l r = ⟨ inj₂ (l , r) ⟩

  aTree : μ TreeC ℕ
  aTree = node (leaf 0) (leaf 1)

  -- Rose trees
  RoseC : Code
  RoseC = P ⊗ (ListC ⊚ I)

  fork : {A : Set} → A → μ ListC (μ RoseC A) → μ RoseC A
  fork x xs = ⟨ x , xs ⟩

  -- Trees with lists on the leaves
  TreeListC : Code
  TreeListC = (ListC ⊚ P) ⊕ (I ⊗ I)

  aTreeOfLists : μ TreeListC ℕ
  aTreeOfLists = ⟨ inj₂ (⟨ inj₁ (cons 0 nil) ⟩ , ⟨ inj₁ (cons 1 nil) ⟩) ⟩

  data TL (A : Set) : Set where
    nodeTL : TL A → TL A → TL A
    leafTL : μ ListC A → TL A

  fromTL : {A : Set} → TL A → μ TreeListC A
  fromTL (nodeTL l r) = ⟨ inj₂ (fromTL l , fromTL r) ⟩
  fromTL (leafTL x  ) = ⟨ inj₁ x ⟩

  toTL : {A : Set} → μ TreeListC A → TL A
  toTL ⟨ inj₁ x ⟩        = leafTL x
  toTL ⟨ inj₂ (l , r) ⟩  = nodeTL (toTL l) (toTL r)
