{-# OPTIONS --type-in-type #-}
module Fold where

open import Prelude
open import IxFun
open import List
open import RoseTree
open import Perfect
-- open import AST

-- force reduction
⟦[_]⟧ : ∀ {I O} → Code I O → I ▷ O
⟦[ C ]⟧ = λ r o → ⟦ C ⟧ r o

Alg : {I O : Set} → Code I O → Indexed I → Indexed O → Indexed O
Alg Z          r s o = ⊤
Alg U          r s o = s o
Alg (K A)      r s o = A → s o
Alg (I i)      r s o = r i → s o
Alg (X R F)    r s o = ∀ {o′} → R o o′ → Alg F r {!s!} o′ -- I do not know what to put here
Alg (Y f F)    r s o = Alg F (λ i′ → r (f i′)) s o
Alg (F ⊕ G)    r s o = Alg F r s o × Alg G r s o
Alg (F ⊗ G)    r s o = Alg F r (Alg G r s) o
Alg (F ⊚ G)    r s o = Alg F (⟦[ G ]⟧ r) s o
Alg (! o′)     r s o = s o′
Alg (Fix F)    r s o = ⟦[ Fix F ]⟧ r o → s o
Alg (Σ f)     r s o = ∀ x → Alg (f x) r s o
{-
Alg (EP C D e) r s o with e r o 
Alg (EP C D e) r s o | ep from to = Alg C r s o
-}
Alg (EP C D e) r s o = Alg C r s o

RawAlg : {I O : Set} → Code I O → Indexed I → Indexed O → Indexed O
RawAlg C r s o = ⟦ C ⟧ r o → s o

Algebra : {I O : Set} → Code (I + O) O → Indexed I → Indexed O → Set
Algebra {O = O} C = λ r s → (o : O) → Alg C (r ∣ s) s o

RawAlgebra : {I O : Set} → Code (I + O) O → Indexed I → Indexed O → Set
RawAlgebra {O = O} C r s = (o : O) → RawAlg C (r ∣ s) s o

runAlg : {I O : Set} {r : Indexed I} {s : Indexed O} → (C : Code I O) →
             Alg C r s ⇉ RawAlg C r s
runAlg Z          o  φ         ()
runAlg U          o  φ         x       = φ
runAlg (K A)      o  φ         x       = φ x
runAlg (I i)      o  φ         x       = φ x
runAlg (X R F)    o  φ         (some {o′} (p , x)) = runAlg F o′ (φ p) x
runAlg (Y f F)    o  φ         x       = runAlg F o φ x
runAlg (F ⊕ G)    o  (φ₁ , φ₂) (inl x) = runAlg F o φ₁ x
runAlg (F ⊕ G)    o  (φ₁ , φ₂) (inr x) = runAlg G o φ₂ x
runAlg (F ⊗ G)    o  φ         (x , y) = runAlg G o (runAlg F o φ x) y
runAlg (F ⊚ G)    o  φ         x       = runAlg F o φ x
runAlg (! o)      .o φ         refl    = φ
runAlg (Fix F)    o  φ         x       = φ x
runAlg (Σ f)     o  φ         (some {x} y) = runAlg (f x) o (φ x) y
runAlg {r = r} (EP C D e) o φ x with e r o 
runAlg (EP C D e) o φ x | ep from _ = runAlg C o φ (from x)

runAlgebra : {I O : Set} {r : Indexed I} {s : Indexed O} → (C : Code (I + O) O) →
             Algebra C r s → RawAlgebra C r s
runAlgebra C φ o = runAlg C o (φ o)

fold : {I O : Set} {r : Indexed I} {s : Indexed O} → (C : Code (I + O) O) →
       Algebra C r s → ⟦ Fix C ⟧ r ⇉ s
fold C φ o x = cata C (runAlgebra C φ) o x

foldK : {I O : Set} {r : Indexed I} {R : Set} → (C : Code (I + O) O) →
        Algebra C r (const R) → (o : O) → ⟦ Fix C ⟧ r o → R
foldK = fold

foldList : {A R : Set} → (R × (A → R → R)) → List A → R
foldList φ xs = foldK `ListF' (const φ) tt (fromList xs)

len : ∀ {A} → List A → Nat
len = foldList (zero , const suc)