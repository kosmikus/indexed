{-# OPTIONS --type-in-type #-}
module Enum where

open import Prelude
open import IxFun
--open import List
--open import RoseTree
--open import Perfect
-- open import AST

-- Codata basics
codata ∞ (T : Set) : Set where
  ♯_ : T → ∞ T

♭ : ∀ {T} → ∞ T → T
♭ (♯ x) = x


-- Stream type
infixr 6 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : (h : A) → (t : ∞ (List A)) → List A


-- Utilitiess on streams
_++_ : {A : Set} → List A → List A → List A
[]        ++ l = l
(h ∷ ♯ t) ++ l = h ∷ ♯ (t ++ l)

single : {A : Set} (a : A) → List A
single x = x ∷ ♯ []

mapList : {A B : Set} → (A -> B) → List A → List B
mapList f []          = []
mapList f (h ∷ (♯ t)) = f h ∷ ♯ (mapList f t)

-- interleave
infixr 5 _⋎_
_⋎_ : ∀ {A} → List A → List A → List A
[]       ⋎ ys = ys
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

-- | Diagonalization of nested lists. Ensure that some elements from every
-- sublist will be included. Handles infinite sublists.
--
-- From Mark Jones' talk at AFP2008
foldrList : {A B : Set} → (A → B → B) → B → List A → B
foldrList c n []          = n
foldrList c n (h ∷ (♯ t)) = c h (foldrList c n t)

concatList : {A : Set} → List (List A) → List A
concatList (l ∷ ls) = l ++ concatList (♭ ls)
concatList []       = []

combine : {A : Set} → (A → A → A) → List A → List A → List A
combine _ xs       []       = xs
combine _ []       ys       = ys
combine f (x ∷ xs) (y ∷ ys) = f x y ∷ ♯ (combine f (♭ xs) (♭ ys))

skew : {A : Set} → List (List A) → List (List A) → List (List A)
skew []           ys = ys
skew (x ∷ (♯ xs)) ys = x ∷ ♯ (combine _++_ xs ys)

diag : {A : Set} → List (List A) -> List A
diag = concatList ∘ foldrList skew [] ∘ mapList (mapList single)


enum : {I O : Set} {r : Indexed I} {o : O} (C : Code I O) → List (⟦ C ⟧ r o)
enum Z = []
enum U = single tt
enum (I i) = [] --wrong
enum (X R F) = []
enum (Y y F) = [] --mapList (map F (λ i f → {!!}) _) (enum F)
enum (F ⊕ G) = mapList inl (enum F) ⋎ mapList inr (enum G)
enum (F ⊗ G) = prod (enum F) (enum G) where
                 prod : {A B : Set} → List A → List B → List (A × B)
                 prod []          _ = []
                 prod (h ∷ (♯ t)) l = mapList (λ y → h , y) l ⋎ prod t l
enum (F ⊚ G) with enum F | enum G
enum {o = o} (F ⊚ G) | ef | eg = diag (mapList (λ x → mapList (map F (λ _ f → f x) o) ef) eg)
enum (! o′) = []
enum (Σ y) = []
enum {o = o} (Fix F) = mapList ⟨_⟩ (enum F) -- wrong
enum {r = r} {o = o} (EP C D e) with e r o
enum (EP C D e) | ep from to = mapList to (enum C)
