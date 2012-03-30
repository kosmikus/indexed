{-# OPTIONS --no-termination-check #-}

-- m datatypes, n parameters
-- (allows flexible composition; allows integrated Fix)
module Indexed where

open import Prelude hiding (Rec)

data Code (Ix : Set) (Ox : Set) : Set₁ where
  U   : Code Ix Ox
  I   : Ix → Code Ix Ox
  !   : Ox → Code Ix Ox
  K   : (X : Set) → Code Ix Ox
  _⊕_ : (F G : Code Ix Ox) → Code Ix Ox
  _⊗_ : (F G : Code Ix Ox) → Code Ix Ox
  _⊚_ : {Mx : Set} → (F : Code Mx Ox) (G : Code Ix Mx) → Code Ix Ox
  Fix : (F : Code (Ix ⊎ Ox) Ox) → Code Ix Ox

Code₂ : Set → Set → Set → Set₁
Code₂ Ix Jx Ox = Code (Ix ⊎ Jx) Ox

Indexed : Set → Set₁
Indexed Ix = Ix → Set

_⇉_ : {Ix : Set} → Indexed Ix → Indexed Ix → Set
R ⇉ S = (ix : _) → R ix → S ix

_⇉∘_ : {Ix : Set} {R S T : Indexed Ix} → S ⇉ T → R ⇉ S → R ⇉ T
(f ⇉∘ g) ix i = f ix (g ix i)

id⇉ : {Ix : Set} {R : Indexed Ix} → R ⇉ R
id⇉ i x = x

_∣_ : ∀ {I J} → Indexed I → Indexed J → Indexed (I ⊎ J)
(r ∣ s) (inj₁ i) = r i
(r ∣ s) (inj₂ j) = s j

_∥_ : {Ix Jx : Set} {A C : Indexed Ix} {B D : Indexed Jx} 
    → A ⇉ C → B ⇉ D → (A ∣ B) ⇉ (C ∣ D)
_∥_ f g (inj₁ x) z = f x z
_∥_ f g (inj₂ y) z = g y z

----------------------------------------------------------------------
-- Properties of morphisms
----------------------------------------------------------------------
-- Somehow I cannot avoid importing _≗_, so I name this differently
infix 4 _≅_
_≅_ : ∀ {I : Set}{r s : Indexed I} (f g : r ⇉ s) → Set
f ≅ g = ∀ i x → f i x ≡ g i x

∥cong : {I J : Set}{r u : Indexed I}{s v : Indexed J}{f₁ f₂ : r ⇉ u}{g₁ g₂ : s ⇉ v} →
        f₁ ≅ f₂ → g₁ ≅ g₂ → (f₁ ∥ g₁) ≅ (f₂ ∥ g₂)
∥cong if ig (inj₁ i) x = if i x
∥cong if ig (inj₂ j) x = ig j x

[,]-cong : {I J : Set} {r u : Indexed I} {s v : Indexed J} {f₁ f₂ : r ⇉ u} {g₁ g₂ : s ⇉ v} →
           f₁ ≅ f₂ → g₁ ≅ g₂ → [_,_] {C = λ z → (r ∣ s) z → (u ∣ v) z} f₁ g₁ ≅ [_,_]  f₂ g₂
[,]-cong if ig (inj₁ i) x = if i x
[,]-cong if ig (inj₂ j) x = ig j x


∥id : {I J : Set} {r : Indexed I} {s : Indexed J}{f : r ⇉ r}{g : s ⇉ s} →
      f ≅ id⇉ → g ≅ id⇉ → (f ∥ g) ≅ id⇉
∥id if ig (inj₁ i) x = if i x
∥id if ig (inj₂ j) x = ig j x

[,]-id : {I J : Set} {r : Indexed (I ⊎ J)} → [_,_] id⇉ id⇉ ≅ id⇉ {I ⊎ J} {r}
[,]-id (inj₁ i) x = refl
[,]-id (inj₂ i) x = refl

∥∘ : {I J : Set}{r₁ s₁ t₁ : Indexed I}{r₂ s₂ t₂ : Indexed J} → 
     {f₁ : s₁ ⇉ t₁}{g₁ : r₁ ⇉ s₁}{f₂ : s₂ ⇉ t₂}{g₂ : r₂ ⇉ s₂} →
     ((f₁ ⇉∘ g₁) ∥ (f₂ ⇉∘ g₂)) ≅ ((f₁ ∥ f₂) ⇉∘ (g₁ ∥ g₂))
∥∘ (inj₁ i) x = refl
∥∘ (inj₂ j) x = refl

[,]-∘ : {I J : Set}{r₁ s₁ t₁ : Indexed I}{r₂ s₂ t₂ : Indexed J} → 
        {f₁ : s₁ ⇉ t₁}{g₁ : r₁ ⇉ s₁}{f₂ : s₂ ⇉ t₂}{g₂ : r₂ ⇉ s₂} →
        ([_,_] {C = λ z → (r₁ ∣ r₂) z → (t₁ ∣ t₂) z} (f₁ ⇉∘ g₁) (f₂ ⇉∘ g₂)) ≅
        ([_,_] {C = λ z → (s₁ ∣ s₂) z → (t₁ ∣ t₂) z} f₁ f₂ ⇉∘ [ g₁ , g₂ ])
[,]-∘ (inj₁ i) x = refl
[,]-∘ (inj₂ j) x = refl

----------------------------------------------------------------------
-- Interpretation
----------------------------------------------------------------------
mutual
  ⟦_⟧ : {Ix Ox : Set} → Code Ix Ox → Indexed Ix → Indexed Ox
  ⟦ U ⟧     R ix = ⊤
  ⟦ I xi ⟧  R ix = R xi
  ⟦ ! xi ⟧  R ix = ix ≡ xi
  ⟦ K X ⟧   R ix = X
  ⟦ F ⊕ G ⟧ R ix = ⟦ F ⟧ R ix ⊎ ⟦ G ⟧ R ix
  ⟦ F ⊗ G ⟧ R ix = ⟦ F ⟧ R ix × ⟦ G ⟧ R ix 
  ⟦ F ⊚ G ⟧ R ix = ⟦ F ⟧ (⟦ G ⟧ R) ix
  ⟦ Fix F ⟧ R ix = μ F R ix

  data μ {Ix Ox : Set} (F : Code₂ Ix Ox Ox) (r : Indexed Ix) (o : Ox) : Set where
    ⟨_⟩ : ⟦ F ⟧ (r ∣ μ F r) o → μ F r o

inn : {Ix Ox : Set} {F : Code₂ Ix Ox Ox} {r : Indexed Ix} {o : Ox}
    → μ F r o → ⟦ F ⟧ (r ∣ μ F r) o
inn ⟨ x ⟩ = x

----------------------------------------------------------------------
-- Map
----------------------------------------------------------------------
map : {Ix Ox : Set} (F : Code Ix Ox) → {R S : Indexed Ix} → (R ⇉ S) → ⟦ F ⟧ R ⇉ ⟦ F ⟧ S
map U       f ix _        = tt
map (I xi)  f ix x        = f xi x
map (! xi)  f ix x        = x
map (K X)   f ix x        = x
map (F ⊕ G) f ix (inj₁ x) = inj₁ (map F f ix x)
map (F ⊕ G) f ix (inj₂ y) = inj₂ (map G f ix y)
map (F ⊗ G) f ix (x ,, y) = map F f ix x ,, map G f ix y
map (F ⊚ G) f ix x        = map F (map G f) ix x
map (Fix F) f ix ⟨ x ⟩    = ⟨ map F (f ∥ map (Fix F) f) ix x ⟩

----------------------------------------------------------------------
-- Map laws
----------------------------------------------------------------------
map-cong : {I O : Set}{r s : Indexed I}{f g : r ⇉ s}→
           (C : Code I O) → f ≅ g →
           map C f ≅ map C g
map-cong U           ip i x        = refl
map-cong (I i′)      ip i x        = ip i′ x
map-cong (K X)       ip i x        = refl
map-cong (F ⊕ G)     ip i (inj₁ x) = cong inj₁ (map-cong F ip i x)
map-cong (F ⊕ G)     ip i (inj₂ x) = cong inj₂ (map-cong G ip i x)
map-cong (F ⊗ G)     ip i (x ,, y) = cong₂ _,,_ (map-cong F ip i x) (map-cong G ip i y)
map-cong (F ⊚ G)     ip i x        = map-cong F (map-cong G ip) i x
map-cong (! o′)      ip i x        = refl
map-cong (Fix F)     ip i ⟨ x ⟩    = cong ⟨_⟩ (map-cong F (∥cong ip (map-cong (Fix F) ip)) i x)

map-id : {I O : Set}{r : Indexed I}(C : Code I O) →
         map C {R = r} id⇉ ≅ id⇉
map-id U          i x        = refl
map-id (I i′)     i x        = refl
map-id (K X)      i x        = refl
map-id (F ⊕ G)    i (inj₁ x) = cong inj₁ (map-id F i x)
map-id (F ⊕ G)    i (inj₂ x) = cong inj₂ (map-id G i x)
map-id (F ⊗ G)    i (x ,, y) = cong₂ _,,_ (map-id F i x) (map-id G i y)
map-id (F ⊚ G)    i x        = trans (map-cong F (map-id G) i x) (map-id F i x)
map-id (! o′)     i x        = refl
map-id (Fix F)    i ⟨ x ⟩    = cong ⟨_⟩ (trans (map-cong F (∥id (λ _ _ → refl)
                                                           (map-id (Fix F))) i x)
                                               (map-id F i x))

map-∘ : {I O : Set} {r s t : Indexed I}
        (C : Code I O) (f : s ⇉ t) (g : r ⇉ s)
      → map C (f ⇉∘ g) ≅ map C f ⇉∘ map C g
map-∘ U           f g i x        = refl
map-∘ (I i′)      f g i x        = refl
map-∘ (K X)       f g i x        = refl
map-∘ (F ⊕ G)     f g i (inj₁ x) = cong inj₁ (map-∘ F f g i x)
map-∘ (F ⊕ G)     f g i (inj₂ x) = cong inj₂ (map-∘ G f g i x)
map-∘ (F ⊗ G)     f g i (x ,, y) = cong₂ _,,_ (map-∘ F f g i x) (map-∘ G f g i y)
map-∘ (F ⊚ G)     f g i x        = trans (map-cong F (map-∘ G f g) i x)
                                         (map-∘ F (map G f) (map G g) i x)
map-∘ (! o′)      f g i x        = refl
map-∘ (Fix F)     f g i ⟨ x ⟩    = cong ⟨_⟩ (trans (map-cong F (∥cong (λ _ _ → refl)
                                                                      (map-∘ (Fix F) f g))
                                                             i x)
                                            (trans (map-cong F ∥∘ i x)
                                                   (map-∘ F (f ∥ map (Fix F) f)
                                                            (g ∥ map (Fix F) g) i x)))


----------------------------------------------------------------------
-- Recursion morphisms
----------------------------------------------------------------------
bimap : {Ix Jx Ox : Set} (F : Code₂ Ix Jx Ox) → {R S : Indexed Ix} {T U : Indexed Jx} →
        (R ⇉ S) → (T ⇉ U) → ⟦ F ⟧ (R ∣ T) ⇉ ⟦ F ⟧ (S ∣ U)
bimap F f g = map F (f ∥ g)

cata : {Ix Ox : Set} {F : Code₂ Ix Ox Ox} {R : Indexed Ix} {S : Indexed Ox} →
       (⟦ F ⟧ (R ∣ S) ⇉ S) → (μ F R ⇉ S)
cata {_} {_} {F} φ ix ⟨ x ⟩ = φ ix (bimap F (λ xi z → z) (cata φ) ix x)

-- Helpers
BiF = Code₂ ⊤ ⊤ ⊤

μ' : BiF → Set → Set
μ' C A = ⟦ Fix C ⟧ (λ _ → A) tt

Par : BiF
Par = I (inj₁ tt)

Rec : BiF
Rec = I (inj₂ tt)

-- Translated PolyP encodings
ListC : BiF
ListC = U ⊕ (Par ⊗ Rec)

nil : {A : Set} → μ' ListC A
nil = ⟨ inj₁ tt ⟩

cons : {A : Set} → A → μ' ListC A → μ' ListC A
cons x xs = ⟨ inj₂ (x ,, xs) ⟩

TreeC : Code (⊤ ⊎ ⊤) ⊤
TreeC = Par ⊕ (Rec ⊗ Rec)

leaf : {A : Set} → A → μ' TreeC A
leaf x = ⟨ inj₁ x ⟩

node : {A : Set} → μ' TreeC A → μ' TreeC A → μ' TreeC A
node l r = ⟨ inj₂ (l ,, r) ⟩

RoseC : Code (⊤ ⊎ ⊤) ⊤
RoseC = Par ⊗ (Fix ListC ⊚ Rec)

fork : {A : Set} → A → μ' ListC (μ' RoseC A) → μ' RoseC A
fork x xs = ⟨ x ,, xs ⟩

open import Data.Nat

aList : μ' ListC ℕ
aList = cons 0 (cons 1 nil)

aTree : μ' TreeC ℕ
aTree = node (leaf 0) (leaf 1)

TreeListC : Code (⊤ ⊎ ⊤) ⊤
TreeListC = (Fix ListC ⊚ Par) ⊕ (Rec ⊗ Rec)

aTreeOfLists : μ' TreeListC ℕ
aTreeOfLists = ⟨ inj₂ (⟨ inj₁ (cons 0 nil) ⟩ ,, ⟨ inj₁ (cons 1 nil) ⟩) ⟩

-- assuming we "believe" that lists are isomorphic
data TL (A : Set) : Set where
  nodeTL : TL A → TL A → TL A
  leafTL : μ' ListC A → TL A

fromTL : {A : Set} → TL A → μ' TreeListC A
fromTL (nodeTL l r) = ⟨ inj₂ (fromTL l ,, fromTL r) ⟩
fromTL (leafTL x  ) = ⟨ inj₁ x ⟩

toTL : {A : Set} → μ' TreeListC A → TL A
toTL ⟨ inj₁ x ⟩        = leafTL x
toTL ⟨ inj₂ (l ,, r) ⟩ = nodeTL (toTL l) (toTL r)


-- A generic function
size : {I O : Set} (C : Code I O) {r : Indexed I} {o : O}
     → ((i : I) → r i → ℕ) → ⟦ C ⟧ r o → ℕ
size U     f x = 1
size (I i) f x = f i x
size (! o) f x = 0
size (K X) f x = 1
size (F ⊕ G) f (inj₁ x) = size F f x
size (F ⊕ G) f (inj₂ x) = size G f x
size (F ⊗ G) f (x ,, y) = size F f x + size G f y
size (F ⊚ G) f x        = size F (λ _ → size G f) x
size (Fix F) f ⟨ x ⟩    = size F g x where
  g : (i : _ ⊎ _) → _ → ℕ
  g (inj₁ i) y = f i y
  g (inj₂ i) y = size (Fix F) f y
