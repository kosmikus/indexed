{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module TestZipper where

open import Prelude hiding (up)
open import IxFun
open import Zipper2
open import Tree
open import Nat

match⊤ : {i : ⊤} {A : Set} → A → A
match⊤ {tt} x = x

-- Zipper for binary trees

t1 : Tree Nat
t1 = node (leaf 1) (leaf 2)

t2 : Tree Nat
t2 = node t1 (node (leaf 3) (leaf 4))

enterTree : ∀ {A} → Tree A → Loc `TreeF' (T A) tt
--enterTree t = loc (fromTree t) empty
--enterTree t = enter (fromTree t)
enterTree t = enterEP epTree t

leaveTree : ∀ {A} → Loc `TreeF' (T A) tt → Maybe (Tree A)
{-
leaveTree (loc x empty)      = just (toTree x)
leaveTree (loc x (push h t)) = up ((loc x (push h t))) >>= leaveTree
-}
leaveTree t = leaveEP epTree t

-- What is best: defining on and update using the generic versions or not?
onTree : ∀ {A i} → Loc `TreeF' (T A) i → Tree A
onTree (loc {i = tt} t _) = toTree t

{-
onTree′ : {i : ⊤} {r : Indexed ⊤} → Loc `TreeF' r i → ∃ (Tree ∘ r)
onTree′ = on toTree′
-}
onTree′ : {A : Set} → Loc `TreeF' (T A) tt → Tree A
onTree′ x with on (λ i → toTree′) x
... | some {tt} y = y

updateTree : ∀ {A i} → (Tree A → Tree A)
           → Loc `TreeF' (T A) i → Maybe (Loc `TreeF' (T A) i)
updateTree f (loc {i = tt} x l) = just (loc (fromTree (f (toTree x))) l)

updateTree′ : ∀ {A i} → (Tree A → Tree A)
           → Loc `TreeF' (T A) i → Maybe (Loc `TreeF' (T A) i)
updateTree′ {A} {tt} f x = just (update g tt x) where
  g : (i : ⊤) → ⟦ `Tree' ⟧ (T A) i → ⟦ `Tree' ⟧ (T A) i
  g tt = fromTree ∘ f ∘ toTree

test1 : Tree Nat → Maybe (Tree Nat)
test1 t = down (enterTree t) >>= 
          updateTree (mapTree (const 0)) >>= 
          leaveTree

-- Get leftmost subtree
test2 : Tree Nat → Tree Nat
test2 t = onTree (f (enterTree t)) where
  f : ∀ {A} → Loc `TreeF' (T A) tt → (Loc `TreeF' (T A) tt)
  f x with (down x)
  f x | nothing = x
  f x | just p  = f p

-- Get rightmost subtree
test3 : Tree Nat → Tree Nat
test3 t = onTree (f (enterTree t)) where
  mutual
    g : ∀ {A} → Loc `TreeF' (T A) tt → (Loc `TreeF' (T A) tt)
    g x with (right x)
    g x | nothing = f x
    g x | just p  = g p
    f : ∀ {A} → Loc `TreeF' (T A) tt → (Loc `TreeF' (T A) tt)
    f x with (down x)
    f x | nothing = x
    f x | just p  = g p


open import ListPair
open import List

lp1 : List (Nat × Nat)
lp1 = (0 , 1) ∷ ((2 , 3) ∷ ((4 , 5) ∷ []))

{-
test41 : List (Nat × Nat) → Maybe (List (Nat × Nat))
test41 lp = down {o = tt} (enter (fromList lp)) >>= just ∘ on to where
    to : (i : ⊤) → ⟦ `List' ⟧ (T (Nat × Nat)) i → List (Nat × Nat)
    to tt = toList

test4 : List (Nat × Nat) → Maybe (List (Nat × Nat))
test4 lp = down {o = tt} (enter (fromListPair′ lp)) >>= just ∘ on to
  where
    from : {i : ⊤} → List (Nat × Nat) → ⟦ `ListPair' ⟧ (T Nat ∣ T Nat) i
    from {tt} = fromListPair′
    to : {i : ⊤} → ⟦ `ListPair' ⟧ (T Nat ∣ T Nat) i → List (Nat × Nat)
    to {tt} = toListPair′
-}

open import Perfect

test5 : {n : Nat} → Perfect Nat {n} → Maybe (Perfect Nat {n})
test5 p = down (enter (fromPerfect p)) >>= 
          just ∙ (update f _)          >>= 
          leave                        >>=
          just ∙ toPerfect where
  f : (n : Nat) → ⟦ `Perfect' ⟧ (T Nat) n → ⟦ `Perfect' ⟧ (T Nat) n
  f n p = fromPerfect
              (cataPerfect′ {R = λ n → Perfect Nat {n}} leaf (λ a p' → split a (swap p'))
                (toPerfect p))


open import RoseTree

test6 : Rose Nat → Maybe (Rose Nat)
test6 t = down (enter (fromRose t)) >>=
          right >>= right >>= right >>= down >>=
          just ∙ (update f _) >>= 
          leave >>=
          just ∙ toRose where
  f : (i : ⊤) → ⟦ `Rose' ⟧ (T Nat) i → ⟦ `Rose' ⟧ (T Nat) i
  f tt = map `Rose' (↑ suc) tt


open import AST

test7 : Expr Nat → Maybe (Expr Nat)
test7 e = let f : (i : AST) → _
              f i = map `AST' (↑ {Nat} suc) i
          in down (enter (fromExpr e)) >>=
             just ∙ update f _ >>=
             right >>= just ∙ update f _ >>=
             leave >>=
             just ∙ toExpr
