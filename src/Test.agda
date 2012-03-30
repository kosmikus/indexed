{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}

module Test where

open import Nat
open import Prelude hiding (up)
open import IxFun
open import Zipper
open import Tree

match⊤ : {i : ⊤} {A : Set} → A → A
match⊤ {tt} x = x

-- Zipper for binary trees

t1 : Tree Nat
t1 = node (leaf 1) (leaf 2)

t2 : Tree Nat
t2 = node t1 (node (leaf 3) (leaf 4))

-- Obtain the first element of a structure
firstElem : {A : Set} (C : ⊤ ▸ ⊤) → ⟦ C ⟧ (λ _ → A) tt → Maybe A
firstElem C x = first C (λ _ x _ → just x) x

-- Sample use of firstElem
treeElem : firstElem `TreeE' t2 ≡ just 1
treeElem = refl

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

-- test3 {t1,t2}

open import List

-- Some experiments on lists of lists
`ListList' = `ListE' ⊚ `ListE'

-- Get the first element (plus the associated context) of a list of lists.
firstListList : List (List Nat) → Maybe (Nat × Ctx `ListList' tt (const Nat) tt)
firstListList xss = first `ListList' f xss
  where
    f : (i : ⊤) → Nat → Ctx `ListList' i (const Nat) tt → Maybe (Nat × Ctx `ListList' tt (const Nat) tt)
    f tt n c = just (n , c)

-- Get the next element (plus the associated context) of a list of lists.
nextListList : (Nat × Ctx `ListList' tt (const Nat) tt) → Maybe (Nat × Ctx `ListList' tt (const Nat) tt)
nextListList (n , c) = next `ListList' f c n
  where
    f : (i : ⊤) → Nat → Ctx `ListList' i (const Nat) tt → Maybe (Nat × Ctx `ListList' tt (const Nat) tt)
    f tt n c = just (n , c)

-- Iterate through contexts and collect the elements in a list.
iterate : {A B : Set} → ((A × B) → Maybe (A × B)) → Maybe (A × B) → List A
iterate f nothing        = []
iterate f (just (x , y)) = x ∷ iterate f (f (x , y))

-- A test list of lists.
ll1 : List (List Nat)
ll1 = [] ∷ (1 ∷ 2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ []

-- Iterating over ll1 should flatten the list.
tll1 : iterate nextListList (firstListList ll1) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [])
tll1 = refl


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

-- test5 p4

open import RoseTree

test6 : Rose Nat → Maybe (Rose Nat)
test6 t = down (enter (fromRose t)) >>=
          right >>= right >>= right >>= down >>=
          just ∙ (update f _) >>= 
          leave >>=
          just ∙ toRose where
  f : (i : ⊤) → ⟦ `Rose' ⟧ (T Nat) i → ⟦ `Rose' ⟧ (T Nat) i
  f tt = map `Rose' (↑ suc) tt

-- test6 r2

open import AST

test7 : Expr Nat → Maybe (Expr Nat)
test7 e = let f : (i : AST) → _
              f i = map `AST' (↑ {Nat} suc) i
          in down (enter (fromExpr e)) >>=
             just ∙ update f _ >>=
             right >>= just ∙ update f _ >>=
             leave >>=
             just ∙ toExpr

-- test7 expr1
