{-# OPTIONS --no-termination-check #-}
{-# OPTIONS --type-in-type         #-}

-- 1 datatype, 0 parameters
module Regular where

  open import Prelude

  data Code : Set₁ where
    U   : Code
    I   : Code
    K   : (X : Set) → Code
    _⊕_ : (F G : Code) → Code
    _⊗_ : (F G : Code) → Code

  ⟦_⟧ : Code → (Set → Set)
  ⟦ U ⟧     A = ⊤
  ⟦ I ⟧     A = A
  ⟦ K X ⟧   A = X
  ⟦ F ⊕ G ⟧ A = ⟦ F ⟧ A ⊎ ⟦ G ⟧ A
  ⟦ F ⊗ G ⟧ A = ⟦ F ⟧ A × ⟦ G ⟧ A

  foldRegular : {A : Set} (C : Code) {R : Code → Set}
              → R U → (A → R I) → (∀ X → (x : X) → R (K X)) 
              → (∀ C D → R C → R (C ⊕ D)) → (∀ C D → R D → R (C ⊕ D)) 
              → (∀ C D → R C → R D → R (C ⊗ D))
              → ⟦ C ⟧ A → R C
  foldRegular U       u i k p₁ p₂ t x = u
  foldRegular I       u i k p₁ p₂ t x = i x
  foldRegular (K X)   u i k p₁ p₂ t x = k X x
  foldRegular (F ⊕ G) u i k p₁ p₂ t (inj₁ x) = p₁ F G (foldRegular F u i k p₁ p₂ t x)
  foldRegular (F ⊕ G) u i k p₁ p₂ t (inj₂ x) = p₂ F G (foldRegular G u i k p₁ p₂ t x)
  foldRegular (F ⊗ G) u i k p₁ p₂ t (x , y)  = t  F G (foldRegular F u i k p₁ p₂ t x)
                                                      (foldRegular G u i k p₁ p₂ t y)
{-
  test : {A : Set} (C : Code) {f g : Code → _} → ⟦ C ⟧ A → (f C ≡ g C)
  test {A} C {f} {g} = foldRegular {A} C {{!λ c → f c ≡ g c!}} refl refl (const refl) (λ c₁ c₂ → cong inj₁) (λ c₁ c₂ → cong inj₂) (λ c₁ c₂ → cong₂ _,_)
-}

  data μ (F : Code) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) → μ F

  map : (F : Code) → {A B : Set} → (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B
  map U f _ = tt
  map I f x = f x
  map (K X) f x = x
  map (F ⊕ G) f (inj₁ x) = inj₁ (map F f x)
  map (F ⊕ G) f (inj₂ y) = inj₂ (map G f y)
  map (F ⊗ G) f (x , y) = map F f x , map G f y

  -- Some laws about map
  map∀ : {C : Code} {A B : Set} (f g : A → B) → (∀ x → f x ≡ g x) → (∀ x → map C f x ≡ map C g x)
  map∀ {U} f g p x = refl
  map∀ {I} f g p x = p x
  map∀ {K X} f g p x = refl
  map∀ {F ⊕ G} f g p (inj₁ x) = cong inj₁ (map∀ {F} f g p x)
  map∀ {F ⊕ G} f g p (inj₂ x) = cong inj₂ (map∀ {G} f g p x)
  map∀ {F ⊗ G} f g p (x , y)  = cong₂ _,_ (map∀ {F} f g p x) (map∀ {G} f g p y)

  map∘ : {A B C : Set} (D : Code) {f : B → C} {g : A → B} {x : ⟦ D ⟧ A}
            → map D f (map D g x) ≡ map D (f ∘ g) x
  map∘ U = refl
  map∘ I {_} = refl
  map∘ (K X) = refl
  map∘ (F ⊕ G) {x = inj₁ _} = cong inj₁ (map∘ F)
  map∘ (F ⊕ G) {x = inj₂ _} = cong inj₂ (map∘ G)
  map∘ (F ⊗ G) {x = _ , _}  = cong₂ _,_ (map∘ F) (map∘ G)

  mapId : ∀ {A} (C : Code) {x : ⟦ C ⟧ A} → map C id x ≡ x
  mapId U {tt} = refl
  mapId I = refl
  mapId (K X) = refl
  mapId (F ⊕ G) {inj₁ _} = cong inj₁ (mapId F)
  mapId (F ⊕ G) {inj₂ _} = cong inj₂ (mapId G)
  mapId (F ⊗ G) {_ , _}  = cong₂ _,_ (mapId F) (mapId G)

  -- TODO: fix termination check?
  cata : {F : Code} {A : Set} → (⟦ F ⟧ A → A) → (μ F → A)
  cata {F} φ ⟨ x ⟩ = φ (map F (cata φ) x)

  -- Natural numbers
  NatC : Code
  NatC = U ⊕ I

  aNat : μ NatC
  aNat = ⟨ inj₂ ⟨ inj₂ ⟨ inj₁ tt ⟩ ⟩ ⟩ -- 2