{-# OPTIONS --no-termination-check #-}

-- n datatypes, 0 parameters
module Multirec where

  open import Prelude

  data Code (Ix : Set) : Set₁ where
    U   : Code Ix
    I   : Ix → Code Ix
    !   : Ix → Code Ix  -- or alternatively tagging
    K   : (X : Set) → Code Ix
    _⊕_ : (F G : Code Ix) → Code Ix
    _⊗_ : (F G : Code Ix) → Code Ix

  Indexed : Set → Set₁
  Indexed Ix = Ix → Set

  _⇉_ : {Ix : Set} → Indexed Ix → Indexed Ix → Set
  R ⇉ S = (ix : _) → R ix → S ix

  ⟦_⟧ : {Ix : Set} → Code Ix → Indexed Ix → Indexed Ix
  ⟦ U ⟧     R ix = ⊤
  ⟦ I xi ⟧  R ix = R xi
  ⟦ ! xi ⟧  R ix = ix ≡ xi
  ⟦ K X ⟧   R ix = X
  ⟦ F ⊕ G ⟧ R ix = ⟦ F ⟧ R ix ⊎ ⟦ G ⟧ R ix
  ⟦ F ⊗ G ⟧ R ix = ⟦ F ⟧ R ix × ⟦ G ⟧ R ix 

  data μ {Ix : Set} (F : Code Ix) (ix : Ix) : Set where
    ⟨_⟩ : ⟦ F ⟧ (μ F) ix → μ F ix

  map : {Ix : Set} (F : Code Ix) → {R S : Indexed Ix} → (R ⇉ S) → ⟦ F ⟧ R ⇉ ⟦ F ⟧ S
  map U f ix _ = tt
  map (I xi) f ix x = f xi x
  map (! xi) f ix x = x
  map (K X) f ix x = x
  map (F ⊕ G) f ix (inj₁ x) = inj₁ (map F f ix x)
  map (F ⊕ G) f ix (inj₂ y) = inj₂ (map G f ix y)
  map (F ⊗ G) f ix (x ,, y) = map F f ix x ,, map G f ix y

  cata : {Ix : Set} {F : Code Ix} {R : Indexed Ix} → (⟦ F ⟧ R ⇉ R) → (μ F ⇉ R)
  cata {_} {F} φ ix ⟨ x ⟩ = φ ix (map F (cata φ) ix x)
