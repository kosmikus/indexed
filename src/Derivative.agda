module Derivative where

import Data.Empty
import Data.Unit
import Data.Nat
import Data.Fin
import Data.Fin.Props
import Data.Product
import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Base where

  open Data.Empty
  open Data.Unit
  open Data.Nat
  open Data.Fin
  open Data.Product
  open Data.Sum

  -- Agda code following Conor's original "derivative" paper.
  --
  -- This is more or less exactly the same thing, with the
  -- difference that we're using Agda syntax, and I have replaced
  -- name-based substitution by de-Bruijn-substitution.

  -- Codes for polynomial functors in finitely many variables.
  data Poly : ℕ → Set₁ where

    Z    : {n : ℕ} → Poly n                          -- empty
    U    : {n : ℕ} → Poly n                          -- unit
    _⊕_  : {n : ℕ} → Poly n → Poly n → Poly n        -- sum
    _⊗_  : {n : ℕ} → Poly n → Poly n → Poly n        -- product

    I    : {n : ℕ} → Fin n → Poly n                  -- identity
    μ    : {n : ℕ} → Poly (suc n) → Poly n           -- fixed point
    _[_] : {n : ℕ} → Poly (suc n) → Poly n → Poly n  -- substitution
    ^    : {n : ℕ} → Poly n → Poly (suc n)           -- weakening

  -- Only the final four actually deal with the variables.
  --
  -- In I, we indicate which variable we recurse on.
  -- In μ, we always operate on the first variable.
  -- In F [ G ], we intend to replace the first variable
  --   of F with G.
  -- In ^, we assume an extra variable that isn't used anywhere.

  -- An environment of length n is a telescope of n types.
  -- Each type may refer to its predecessors.
  data Env : ℕ → Set₁ where
    []  : Env 0
    _,_ : {n : ℕ} → Env n → Poly n → Env (suc n)

  -- The interpretation function. The termination checker doesn't
  -- like it -- I think due to substitution adding things to the
  -- environment which is then used in identity. Anyway, there
  -- shouldn't be any surprises here.
  mutual
    ⟦_⟧ : {n : ℕ} → Poly n → Env n → Set
    ⟦ I zero ⟧    (Xs , X) = ⟦ X ⟧ Xs
    ⟦ I (suc i) ⟧ (Xs , X) = ⟦ I i ⟧ Xs
    ⟦ Z ⟧         Xs       = ⊥
    ⟦ U ⟧         Xs       = ⊤
    ⟦ F ⊕ G ⟧     Xs       = ⟦ F ⟧ Xs ⊎ ⟦ G ⟧ Xs
    ⟦ F ⊗ G ⟧     Xs       = ⟦ F ⟧ Xs × ⟦ G ⟧ Xs
    ⟦ μ F ⟧       Xs       = Fix F Xs
    ⟦ F [ G ] ⟧   Xs       = ⟦ F ⟧ (Xs , G)
    ⟦ ^ F ⟧       (Xs , X) = ⟦ F ⟧ Xs

    data Fix {n : ℕ} (F : Poly (suc n)) (Xs : Env n) : Set where
      ⟨_⟩ : ⟦ F ⟧ (Xs , μ F) → Fix F Xs

-- Some examples.
module Examples where

  open Base
  open import Data.Nat hiding (zero; suc)
  open import Data.Sum
  open import Data.Unit
  open import Data.Fin renaming (zero to fzero; suc to fsuc)
  open import Data.Product

  `Bool' : {n : ℕ} → Poly n
  `Bool' = U ⊕ U

  Bool : {n : ℕ} → Env n → Set
  Bool = ⟦ `Bool' ⟧

  true : {n : ℕ} {Γ : Env n} → Bool Γ
  true = inj₁ tt

  false : {n : ℕ} {Γ : Env n} → Bool Γ
  false = inj₂ tt

  `Nat' : {n : ℕ} → Poly n
  `Nat' = μ (U ⊕ I fzero)

  Nat : {n : ℕ} → Env n → Set
  Nat = ⟦ `Nat' ⟧

  zero : {n : ℕ} {Γ : Env n} → Nat Γ
  zero = ⟨ inj₁ tt ⟩

  suc : {n : ℕ} {Γ : Env n} → Nat Γ → Nat Γ
  suc n = ⟨ inj₂ n ⟩

  `Tree' : {n : ℕ} → Poly n
  `Tree' = μ (U ⊕ (I fzero ⊗ I fzero))

  Tree : {n : ℕ} → Env n → Set
  Tree = ⟦ `Tree' ⟧

  leaf : {n : ℕ} {Γ : Env n} → Tree Γ
  leaf = ⟨ inj₁ tt ⟩

  node : {n : ℕ} {Γ : Env n} → Tree Γ → Tree Γ → Tree Γ
  node l r = ⟨ inj₂ (l , r) ⟩

  `List' : {n : ℕ} → Poly n → Poly n
  `List' A = μ (U ⊕ (^ A ⊗ I fzero))

  List : {n : ℕ} → Poly n → Env n → Set
  List A = ⟦ `List' A ⟧
  
  nil : {n : ℕ} {Γ : Env n} {A : Poly n} → List A Γ
  nil = ⟨ inj₁ tt ⟩

  cons : {n : ℕ} {Γ : Env n} {A : Poly n} →
         ⟦ A ⟧ Γ → List A Γ → List A Γ
  cons x xs = ⟨ inj₂ (x , xs) ⟩

module Derivative where

  open Base
  open Data.Empty
  open Data.Unit
  open Data.Nat
  open Data.Fin
  open Data.Fin.Props renaming (_≟_ to _≟f_)
  open Data.Product
  open Data.Sum

  -- The derivative takes a code to a code. This is quite nice, because it
  -- means that we can in principle take the derivative of a derivative.
  --
  -- Note further that this is a partial derivative. It takes a variable
  -- as an argument.
  ∂ : {n : ℕ} → (i : Fin n) → Poly n → Poly n
  ∂ i       (I j)  with i ≟f j
  ∂ i       (I .i) | yes refl = U
  ...              | no  _    = Z
  ∂ i       Z                 = Z
  ∂ i       U                 = Z
  ∂ i       (F ⊕ G)           = ∂ i F ⊕ ∂ i G
  ∂ i       (F ⊗ G)           = (∂ i F ⊗ G) ⊕ (F ⊗ ∂ i G)
  ∂ i       (μ F)             = μ (   ^ (∂ (suc i) F [ μ F ])
                                   ⊕ (^ (∂ zero    F [ μ F ]) ⊗ I zero))
  ∂ i       (F [ G ])         =          ∂ (suc i) F [ G ]
                                      ⊕ (∂ zero    F [ G ]    ⊗ ∂ i G) 
  ∂ zero    (^ F)       = Z
  ∂ (suc i) (^ F)       = ^ (∂ i F)

  -- Plugging takes a derivative and a suitable argument and merges the
  -- two together.
  plug : {n : ℕ} {F : Poly n} {Γ : Env n} {i : Fin n} →
         ⟦ ∂ i F ⟧ Γ → ⟦ I i ⟧ Γ → ⟦ F ⟧ Γ
  plug {F = Z}            ()                 x
  plug {F = U}            ()                 x
  plug {F = I j}  {i = i} cx x with i ≟f j
  plug {F = I .i} {i = i} cx                 x | yes refl = x
  plug {F = I j}  {i = i} ()                 x | no  _
  plug {F = F ⊕ G}        (inj₁ cx)          x = inj₁ (plug {F = F} cx x)
  plug {F = F ⊕ G}        (inj₂ cy)          y = inj₂ (plug {F = G} cy y)
  plug {F = F ⊗ G}        (inj₁ (cx , y))    x = plug {F = F} cx x , y
  plug {F = F ⊗ G}        (inj₂ (x , cy))    y = x , plug {F = G} cy y
  plug {F = F [ G ]} {Γ = Xs} {i = i}
                          (inj₁ cx)          x =   plug {F = F} {Γ = Xs , G}   {i = suc i} cx x
  plug {F = F [ G ]} {Γ = Xs} {i = i}
                          (inj₂ (cz , cx))   x =   plug {F = F} {Γ = Xs , G}   {i = zero}  cz
                                                        (plug {F = G} {Γ = Xs} {i = i} cx x)
  plug {F = μ F}     {Γ = Xs} {i = i}
                          ⟨ inj₁ cx ⟩        x = ⟨ plug {F = F} {Γ = Xs , μ F} {i = suc i} cx x ⟩
  plug {F = μ F}     {Γ = Xs} {i = i}
                          ⟨ inj₂ (cz , cx) ⟩ x = ⟨ plug {F = F} {Γ = Xs , μ F} {i = zero}  cz
                                                        (plug {F = μ F} {Γ = Xs} {i = i} cx x) ⟩
  plug {F = ^ F}              {i = zero}
                          ()                 x
  plug {F = ^ F}     {Γ = Xs , X} {i = suc i}
                          cx                 x = plug {F = F} {Γ = Xs} {i = i} cx x
