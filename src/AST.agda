{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module AST where

open import Nat
open import Prelude
open import IxFun

----------------------------------------------------------------------
-- AST
----------------------------------------------------------------------

{-
-- Index type
AST : Set
AST = ⊤ + ⊤

expr = inl tt
decl = inr tt


-- Codes for the functors (1 parameter, 2 recursive positions)
`ExprF' : Code (⊤ + AST) AST
`ExprF' =   K Nat
          ⊕ I (inr expr) ⊗ I (inr expr)
          ⊕ I (inl tt)
          ⊕ I (inr decl) ⊗ I (inr expr)

`DeclF' : Code (⊤ + AST) AST
`DeclF' =   I (inl tt) ⊗ I (inr expr)
          ⊕ I (inr decl) ⊗ I (inr decl)
          ⊕ U


`ASTF' : Code (⊤ + AST) AST
`ASTF' =   ! expr ⊗ `ExprF'
         ⊕ ! decl ⊗ `DeclF'


-- Code for the fixpoint
`AST' : Code ⊤ AST
`AST' = Fix `ASTF'


-- The actual datatypes
mutual
  data Expr (A : Set) : Set where
    econst : Nat -> Expr A
    add    : Expr A -> Expr A -> Expr A
    evar   : A -> Expr A
    elet   : Decl A -> Expr A -> Expr A


  data Decl (A : Set) : Set where
    assign : A -> Expr A -> Decl A
    seq    : Decl A -> Decl A -> Decl A
    none   : Decl A


-- Conversions
mutual
  fromExpr : {A : Set} -> Expr A -> ⟦ `AST' ⟧ (T A) expr
  fromExpr (econst x) = ⟨ inl (refl , inl x) ⟩
  fromExpr (add x y)  = ⟨ inl (refl , inr (inl (fromExpr x , fromExpr y))) ⟩
  fromExpr (evar x)   = ⟨ inl (refl , inr (inr (inl x))) ⟩
  fromExpr (elet d e) = ⟨ inl (refl , inr (inr (inr (fromDecl d , fromExpr e))))⟩

  fromDecl : {A : Set} → Decl A → ⟦ `AST' ⟧ (T A) decl
  fromDecl (assign x e) = ⟨ inr (refl , inl (x , fromExpr e)) ⟩
  fromDecl (seq d₁ d₂)  = ⟨ inr (refl , inr (inl (fromDecl d₁ , fromDecl d₂)))⟩
  fromDecl none         = ⟨ inr (refl , inr (inr tt))⟩

mutual
  toExpr : {A : Set} → ⟦ `AST' ⟧ (T A) expr → Expr A
  toExpr ⟨ inl (refl , inl x) ⟩                   = econst x
  toExpr ⟨ inl (refl , inr (inl (x , y))) ⟩       = add (toExpr x) (toExpr y)
  toExpr ⟨ inl (refl , inr (inr (inl x))) ⟩       = evar x
  toExpr ⟨ inl (refl , inr (inr (inr (d , e)))) ⟩ = elet (toDecl d) (toExpr e)
  toExpr ⟨ inr (() , _) ⟩

  toDecl : {A : Set} → ⟦ `AST' ⟧ (T A) decl → Decl A
  toDecl ⟨ inl (() , _) ⟩
  toDecl ⟨ inr (refl , inl (x , e)) ⟩         = assign x (toExpr e)
  toDecl ⟨ inr (refl , inr (inl (d₁ , d₂))) ⟩ = seq (toDecl d₁) (toDecl d₂)
  toDecl ⟨ inr (refl , inr (inr tt)) ⟩        = none


IAST : (A : Set) → AST → Set
IAST A (inl tt) = Expr A
IAST A (inr tt) = Decl A

fromAST : {A : Set} → IAST A ⇉ ⟦ `AST' ⟧ (T A)
fromAST (inl tt) e = fromExpr e
fromAST (inr tt) d = fromDecl d

toAST : {A : Set} → ⟦ `AST' ⟧ (T A) ⇉ IAST A
toAST (inl tt) e = toExpr e
toAST (inr tt) d = toDecl d


-- Concrete map
mapExpr : {A B : Set} → (A → B) → Expr A → Expr B
mapExpr f e = toExpr (map `AST' (↑ f) expr (fromExpr e))

mapDecl : {A B : Set} → (A → B) → Decl A → Decl B
mapDecl f d = toDecl (map `AST' (↑ f) decl (fromDecl d))

-- Catamorphism
IASTr : Set → Set → AST → Set
IASTr x _ (inl tt) = x
IASTr _ x (inr tt) = x

cataAST : ∀ {A R R′} → (Nat → R) → (R → R → R) → (A → R) → (R′ → R → R)
                     → (A → R → R′) → (R′ → R′ → R′) → R′
                     → IAST A ⇉ IASTr R R′
cataAST {A} {R} {R′} c p v l a s n i ast =
  cata `ASTF' f i (fromAST i ast)
  where
    f : ⟦ `ASTF' ⟧ (T A ∣ IASTr R R′) ⇉ IASTr R R′
    f (inl tt) (inl (refl , inl y))                    = c y
    f (inl tt) (inl (refl , inr (inl (y , y'))))       = p y y'
    f (inl tt) (inl (refl , inr (inr (inl y))))        = v y
    f (inl tt) (inl (refl , inr (inr (inr (y , y'))))) = l y y'
    f (inl tt) (inr (() , y'))
    f (inr tt) (inl (() , y'))
    f (inr tt) (inr (refl , inl (y , y')))             = a y y'
    f (inr tt) (inr (refl , inr (inl (y , y'))))       = s y y'
    f (inr tt) (inr (refl , inr (inr tt)))             = n
-}

-- Indices
AST : Set
AST = Fin 3

expr : AST
expr = zero

decl : AST
decl = (suc zero)

nat : AST
nat = suc (suc zero)

{-
data ASTView : Fin 3 → Set where
  vnat  : ASTView nat
  vexpr : ASTView expr
  vdecl : ASTView decl

viewAST : (ast : AST) → ASTView ast
viewAST zero             = vexpr
viewAST (suc zero)       = vdecl
viewAST (suc (suc zero)) = vnat
viewAST (suc (suc (suc ())))
-}

-- Codes for the functors (1 parameter, 3 recursive positions)
`ExprF' : (⊤ + AST) ▸ AST
`ExprF' =   I (inr nat)
          ⊕ I (inr expr) ⊗ I (inr expr)
          ⊕ I (inl tt)
          ⊕ I (inr decl) ⊗ I (inr expr)

`DeclF' : (⊤ + AST) ▸ AST
`DeclF' =   I (inl tt)   ⊗ I (inr expr)
          ⊕ I (inr decl) ⊗ I (inr decl)
          ⊕ U

-- Adapting `Nat' to this family
data OWiden {A : Set} : A → ⊤ → Set where
  oWiden : {x : A} → OWiden x tt

`Nat2' : (⊤ + AST) ▸ AST
`Nat2' = `Nat' ↗ (λ ()) ↘ (const tt)

`ASTF' : (⊤ + AST) ▸ AST
`ASTF' =   ! expr ⊗ `ExprF'
         ⊕ ! decl ⊗ `DeclF'
         ⊕ ! nat  ⊗ `Nat2'

-- Code for the fixpoint
`AST' : ⊤ ▸ AST
`AST' = Fix `ASTF'

-- The actual datatypes
mutual
  data Expr (A : Set) : Set where
    econst : Nat -> Expr A
    add    : Expr A -> Expr A -> Expr A
    evar   : A -> Expr A
    elet   : Decl A -> Expr A -> Expr A

  data Decl (A : Set) : Set where
    assign : A -> Expr A -> Decl A
    seq    : Decl A -> Decl A -> Decl A
    none   : Decl A


-- Conversions
mutual
  fromExpr : {r : ⊤ → Set} → Expr (r tt) → ⟦ `AST' ⟧ r expr
  fromExpr (econst x) = ⟨ inl (refl , inl (fromNat2 x)) ⟩
  fromExpr (add x y)  = ⟨ inl (refl , inr (inl (fromExpr x , fromExpr y))) ⟩
  fromExpr (evar x)   = ⟨ inl (refl , inr (inr (inl x))) ⟩
  fromExpr (elet d e) = ⟨ inl (refl , inr (inr (inr (fromDecl d , fromExpr e))))⟩

  fromDecl : {r : ⊤ → Set} → Decl (r tt) → ⟦ `AST' ⟧ r decl
  fromDecl (assign x e) = ⟨ inr (inl (refl , inl (x , fromExpr e))) ⟩
  fromDecl (seq d₁ d₂)  = ⟨ inr (inl (refl , inr (inl (fromDecl d₁ , fromDecl d₂))))⟩
  fromDecl none         = ⟨ inr (inl (refl , inr (inr tt)))⟩

  fromNat2 : {r : ⊤ → Set} → Nat → ⟦ `AST' ⟧ r nat
  fromNat2 n = ⟨ (inr (inr (refl , map {r = (λ ())} `Nat' (λ ()) tt (fromNat n)))) ⟩

mutual
  toExpr : {r : ⊤ → Set} → ⟦ `AST' ⟧ r expr → Expr (r tt)
  toExpr ⟨ inl (refl , inl x) ⟩                   = econst (toNat2 x)
  toExpr ⟨ inl (refl , inr (inl (x , y))) ⟩       = add (toExpr x) (toExpr y)
  toExpr ⟨ inl (refl , inr (inr (inl x))) ⟩       = evar x
  toExpr ⟨ inl (refl , inr (inr (inr (d , e)))) ⟩ = elet (toDecl d) (toExpr e)
  toExpr ⟨ inr (inl (() , _)) ⟩
  toExpr ⟨ inr (inr (() , _)) ⟩

  toDecl : {r : ⊤ → Set} → ⟦ `AST' ⟧ r decl → Decl (r tt)
  toDecl ⟨ inl (() , _) ⟩
  toDecl ⟨ inr (inl (refl , inl (x , e))) ⟩         = assign x (toExpr e)
  toDecl ⟨ inr (inl (refl , inr (inl (d₁ , d₂)))) ⟩ = seq (toDecl d₁) (toDecl d₂)
  toDecl ⟨ inr (inl (refl , inr (inr tt))) ⟩        = none
  toDecl ⟨ inr (inr (() , _)) ⟩

  toNat2 : {r : ⊤ → Set} → ⟦ `AST' ⟧ r nat → Nat
  toNat2 ⟨ inl (() , _) ⟩
  toNat2 ⟨ inr (inl (() , _)) ⟩
  toNat2 ⟨ inr (inr (refl , x)) ⟩ = toNat {r = (λ ())} (map `Nat' (λ ()) tt x)

IAST : (r : ⊤ → Set) → AST → Set
IAST r zero             = Expr (r tt)
IAST r (suc zero)       = Decl (r tt)
IAST _ (suc (suc zero)) = Nat
IAST _ (suc (suc (suc ())))

fromAST : {r : ⊤ → Set} → IAST r ⇉ ⟦ `AST' ⟧ r
fromAST zero                 e = fromExpr e
fromAST (suc zero)           d = fromDecl d
fromAST (suc (suc zero))     n = fromNat2 n
fromAST (suc (suc (suc ()))) _

toAST : {r : ⊤ → Set} → ⟦ `AST' ⟧ r ⇉ IAST r
toAST zero                 e = toExpr e
toAST (suc zero)           d = toDecl d
toAST (suc (suc zero))     n = toNat2 n
toAST (suc (suc (suc ()))) _

postulate isoAST₁ : {i : AST} {r : ⊤ → Set} {x : IAST r i}
                  → toAST i (fromAST i x) ≡ x
postulate isoAST₂ : {i : AST} {r : ⊤ → Set} {x : ⟦ `AST' ⟧ r i}
                  → fromAST i (toAST i x) ≡ x

epAST : (r : ⊤ → Set) (o : AST) → IAST r o ≃ ⟦ `AST' ⟧ r o
epAST r o = record { from = fromAST o ; to = toAST o ; iso₁ = isoAST₁ ; iso₂ = isoAST₂ }

`ASTE' : ⊤ ▸ AST
`ASTE' = Iso `AST' (λ f i → IAST f i) epAST


-- Concrete map
mapAST : {r : ⊤ → Set} {s : ⊤ → Set} → (r tt → s tt) → IAST r ⇉ IAST s
mapAST {r} {s} f i = map `ASTE' g i where
  g : r ⇉ s
  g tt = f

mapExpr : {A B : Set} → (A → B) → Expr A → Expr B
mapExpr {A} {B} f = mapAST {λ _ → A} {λ _ → B} f expr

mapDecl : {A B : Set} → (A → B) → Decl A → Decl B
mapDecl {A} {B} f = mapAST {λ _ → A} {λ _ → B} f decl

mapNat2 : {A B : Set} → (A → B) → Nat → Nat -- identity function
mapNat2 {A} {B} f = mapAST {λ _ → A} {λ _ → B} f nat


-- Catamorphism
IASTr : Set → Set → Set → AST → Set
IASTr x _ _ zero             = x
IASTr _ x _ (suc zero)       = x
IASTr _ _ x (suc (suc zero)) = x
IASTr _ _ _ (suc (suc (suc ())))

cataAST : ∀ {R R′ R′′} → {r : ⊤ → Set}
        → (R′′ → R) → (R → R → R) → ((r tt) → R) → (R′ → R → R)
        → ((r tt) → R → R′) → (R′ → R′ → R′) → R′
        → R′′
        → IAST r ⇉ IASTr R R′ R′′
cataAST {R} {R′} {R′′} {r} c p v l a s n z i ast =
  cata `ASTF' f i (fromAST i ast)
  where
    f : ⟦ `ASTF' ⟧ (r ∣ IASTr R R′ R′′) ⇉ IASTr R R′ R′′
    f zero             (inl (refl , inl x))                     = c x
    f zero             (inl (refl , inr (inl (x1 , x2))))       = p x1 x2
    f zero             (inl (refl , inr (inr (inl x))))         = v x
    f zero             (inl (refl , inr (inr (inr (d , e)))))   = l d e
    f zero             (inr (inl ((), _)))
    f zero             (inr (inr ((), _)))
    f (suc zero)       (inl ((), _))
    f (suc zero)       (inr (inr ((), _)))
    f (suc zero)       (inr (inl (refl , inl (x , e))))         = a x e
    f (suc zero)       (inr (inl (refl , inr (inl (d1 , d2))))) = s d1 d2
    f (suc zero)       (inr (inl (refl , inr (inr tt))))        = n
    f (suc (suc zero)) (inl ((), _))
    f (suc (suc zero)) (inr (inl (() , _)))
    f (suc (suc zero)) (inr (inr (refl , _)))                   = z
    f (suc (suc (suc ()))) _


-- Example values
decl1 : Decl Nat
decl1 = seq (assign 0 (econst 5))
            (seq (assign 1 (econst 6)) none)

expr1 : Expr Nat
expr1 = elet decl1
             (add (evar 0) (evar 1))

-- Increment all variables
exASTMap : IAST (T Nat) ⇉ IAST (T Nat)
exASTMap = mapAST suc
