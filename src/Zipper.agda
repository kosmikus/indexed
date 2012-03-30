{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-termination-check #-}
module Zipper where

open import Prelude hiding (up)
open import IxFun

-- Codes for contexts; would be nice if we could produce a Code again

Ctx : {I O : Set} → Code I O → I → I ▷ O
Ctx Z        i r o = ⊥
Ctx U        i r o = ⊥
Ctx (K A)    i r o = ⊥
Ctx (I i′)   i r o = i ≡ i′
Ctx (X R F)  i r o = ∃ (λ o′ → R o o′ × Ctx F i r o′)
Ctx (Y f F)  i r o = ∃ (λ i′ → (f i′ ≡ i) × Ctx F i′ (r ∘ f) o)
Ctx (F ⊕ G)  i r o = Ctx F i r o + Ctx G i r o
Ctx (F ⊗ G)  i r o = (Ctx F i r o × ⟦ G ⟧ r o) + (⟦ F ⟧ r o × Ctx G i r o)
Ctx (F ⊚ G)  i r o = ∃ (λ m → Ctx F m (⟦ G ⟧ r) o × Ctx G i r m) 
Ctx (! o′)   i r o = ⊥
Ctx (Σ f)   i r o = ∃ (λ i′ → Ctx (f i′) i r o)
Ctx (Fix F)  i r o = Ctx F (inl i) (r ∣ μ F r) o

-- plugging a value into a context
plug : {I O : Set} {r : Indexed I} {i : I} {o : O} →
       (C : Code I O) → Ctx C i r o → r i → ⟦ C ⟧ r o
plug Z       ()                r
plug U       ()                r
plug (K A)   ()                r
plug (I i)   refl              r = r
plug (X R F) (some (p , c))    r = some (p , plug F c r)
plug (Y f F) (some (refl , c)) r = plug F c r
plug (F ⊕ G) (inl c)           r = inl (plug F c r)
plug (F ⊕ G) (inr c)           r = inr (plug G c r)
plug (F ⊗ G) (inl (c , g))     r = plug F c r , g
plug (F ⊗ G) (inr (f , c))     r = f , plug G c r
plug (F ⊚ G) (some (c , d))    r = plug F c (plug G d r)
plug (! o)   ()                r
plug (Σ f)  (some {i} c)      r = some (plug (f i) c r)
plug (Fix F) c                 r = ⟨ plug F c r ⟩

All : {I : Set} → Indexed I
All _ = ⊤

all : {I : Set} → (i : I) → Maybe (All i)
all _ = just tt

OnlyInl : {I O : Set} → Indexed I → Indexed (I + O)
OnlyInl P (inl i) = P i
OnlyInl P (inr _) = ⊥

onlyInl : {I O : Set} {P : Indexed I} → ((i : I) → Maybe (P i))
                                      → (i : (I + O)) → Maybe (OnlyInl P i)
onlyInl d (inl i) = d i
onlyInl d (inr _) = nothing

OnlyInr : {I O : Set} → Indexed O → Indexed (I + O)
OnlyInr P (inl _) = ⊥
OnlyInr P (inr i) = P i

onlyInr : {I O : Set} {P : Indexed O} → ((o : O) → Maybe (P o))
                                      → (o : (I + O)) → Maybe (OnlyInr P o)
onlyInr d (inl _) = nothing
onlyInr d (inr i) = d i

-- The function first takes a functor and splits it (CPS-style) into a
-- value and a context. Splitting can, in general, occur at any (input-)index. We
-- pass a predicate P that describes the indices we want to accept for
-- splitting.

first : {I O : Set} {r : Indexed I} {P : Indexed I} {o : O} {R : Set} →
        (C : Code I O) → ((i : I) → Maybe (P i)) →
        ((i : I) → P i → r i → Ctx C i r o → Maybe R) → 
        ⟦ C ⟧ r o → Maybe R
first Z       π k ()
first U       π k x              = nothing
first (K A)   π k x              = nothing
first (I i)   π k x with π i
first (I i)   π k x | nothing    = nothing
first (I i)   π k x | just φ     = k i φ x refl
first (X R F) π k (some (p , x)) = first F π (λ i φ r c →
                                     k i φ r (some (p , c))) x
first (Y f F) π k x              = first F (λ i′ → π (f i′)) (λ i′ p y c →
                                     k (f i′) p y (some (refl , c))) x
first (F ⊕ G) π k (inl x)        = first F π (λ i φ r c →
                                     k i φ r (inl c)) x
first (F ⊕ G) π k (inr x)        = first G π (λ i φ r c →
                                     k i φ r (inr c)) x
first (F ⊗ G) π k (x , y)        = plusMaybe
                                     (first F π (λ i φ r c →
                                        k i φ r (inl (c , y))) x)
                                     (first G π (λ i φ r c →
                                        k i φ r (inr (x , c))) y)
first (F ⊚ G) π k x              = first F all (λ m _ s c →
                                     first G π (λ i φ r d →
                                       k i φ r (some (c , d))) s) x
first (! o)   π k x              = nothing
first (Σ f)  π k (some {i′} y)  = first (f i′) π (λ i φ r c →
                                       k i φ r (some c)) y
first {J} {O} {r} {P} {o} {R}
      (Fix F) π k ⟨ x ⟩          = first F (onlyInl π) f x
  where
    f : (i : (J + O)) → OnlyInl P i →
        (r ∣ μ F r) i → Ctx F i (r ∣ μ F r) o → Maybe R
    f (inr _) () r c
    f (inl i) φ  r c = k i φ r c

{-
last : {I O : Set} {r : Indexed I} {P : Indexed I} {o : O} {R : Set} →
        (C : Code I O) → ((i : I) → Maybe (P i)) →
        ((i : I) → P i → r i → Ctx C i r o → Maybe R) → 
        ⟦ C ⟧ r o → Maybe R
last Z       π k ()
last U       π k x              = nothing
last (K A)   π k x              = nothing
last (I i)   π k x with π i
last (I i)   π k x | nothing    = nothing
last (I i)   π k x | just φ     = k i φ x refl
last (X R F) π k (some (p , x)) = last F π (λ i φ r c →
                                     k i φ r (some (p , c))) x
last (Y f F) π k x              = last F (λ i′ → π (f i′)) (λ i′ p y c →
                                     k (f i′) p y (some (refl , c))) x
last (F ⊕ G) π k (inl x)        = last F π (λ i φ r c →
                                     k i φ r (inl c)) x
last (F ⊕ G) π k (inr x)        = last G π (λ i φ r c →
                                     k i φ r (inr c)) x
last (F ⊗ G) π k (x , y)        = plusMaybe
                                     (last G π (λ i φ r c →
                                        k i φ r (inr (x , c))) y)
                                     (last F π (λ i φ r c →
                                        k i φ r (inl (c , y))) x)
last (F ⊚ G) π k x              = last F all (λ m _ s c →
                                     last G π (λ i φ r d →
                                       k i φ r (some (c , d))) s) x
last (! o)   π k x              = nothing
last (Σ f)  π k (some {i′} y)  = last (f i′) π (λ i φ r c →
                                       k i φ r (some c)) y
last {J} {O} {r} {P} {o} {R}
      (Fix F) π k ⟨ x ⟩          = last F (onlyInl π) f x
  where
    f : (i : (J + O)) → OnlyInl P i →
        (r ∣ μ F r) i → Ctx F i (r ∣ μ F r) o → Maybe R
    f (inr _) () r c
    f (inl i) φ  r c = k i φ r c
-}

next : {I O : Set} {r : Indexed I} {P : Indexed I} {o : O} {R : Set} →
       (C : Code I O) → ((i : I) → Maybe (P i)) →
       ((i : I) → P i → r i → Ctx C i r o → Maybe R) → 
       {i : I} → Ctx C i r o → r i → Maybe R
next Z       π k ()                r
next U       π k ()                r
next (K A)   π k ()                r
next (I i)   π k c                 r = nothing
next (X R F) π k (some (p , c))    r = next F π (λ i φ s d →
                                         k i φ s (some (p , d))) c r
next (Y f F) π k (some (refl , c)) r = next F (λ i′ → π (f i′)) (λ i′ φ s d →
                                         k (f i′) φ s (some (refl , d))) c r
next (F ⊕ G) π k (inl c)           r = next F π (λ i φ s d →
                                         k i φ s (inl d)) c r
next (F ⊕ G) π k (inr c)           r = next G π (λ i φ s d →
                                         k i φ s (inr d)) c r
next (F ⊗ G) π k (inl (c , g))     r = plusMaybe
                                         (next F π (λ i φ s d →
                                            k i φ s (inl (d , g))) c r)
                                         (first G π (λ i φ s d →
                                            k i φ s (inr (plug F c r , d))) g)
next (F ⊗ G) π k (inr (f , c))     r = next G π (λ i φ s y →
                                         k i φ s (inr (f , y))) c r
next (F ⊚ G) π k (some (c , d))    r = plusMaybe
                                         (next G π (λ i φ s d′ →
                                            k i φ s (some (c , d′))) d r)
                                         (next F all (λ m _ s c′ →
                                            first G π (λ i φ t d′ →
                                              k i φ t (some (c′ , d′))) s)
                                            c (plug G d r))
next (! o′)  π k c                 r = nothing
next (Σ f)  π k (some {i′} c)     r = next (f i′) π (λ i φ s d →
                                         k i φ s (some d)) c r
next {J} {O} {r} {P} {o} {R}
     (Fix F) π k c                 s = next F (onlyInl π) f c s
  where
    f : (i : (J + O)) → OnlyInl P i →
        (r ∣ μ F r) i → Ctx F i (r ∣ μ F r) o → Maybe R
    f (inr _) () r c
    f (inl i) φ  r c = k i φ r c

{-
prev : {I O : Set} {r : Indexed I} {P : Indexed I} {o : O} {R : Set} →
       (C : Code I O) → ((i : I) → Maybe (P i)) →
       ((i : I) → P i → r i → Ctx C i r o → Maybe R) → 
       {i : I} → Ctx C i r o → r i → Maybe R
prev Z       π k ()                r
prev U       π k ()                r
prev (K A)   π k ()                r
prev (I i)   π k c                 r = nothing
prev (X R F) π k (some (p , c))    r = prev F π (λ i φ s d →
                                         k i φ s (some (p , d))) c r
prev (Y f F) π k (some (refl , c)) r = prev F (λ i′ → π (f i′)) (λ i′ φ s d →
                                         k (f i′) φ s (some (refl , d))) c r
prev (F ⊕ G) π k (inl c)           r = prev F π (λ i φ s d →
                                         k i φ s (inl d)) c r
prev (F ⊕ G) π k (inr c)           r = prev G π (λ i φ s d →
                                         k i φ s (inr d)) c r
prev (F ⊗ G) π k (inl (c , g))     r = prev F π (λ i φ s y →
                                         k i φ s (inl (y , g))) c r
prev (F ⊗ G) π k (inr (f , c))     r = plusMaybe
                                         (prev G π (λ i φ s d →
                                            k i φ s (inr (f , d))) c r)
                                         (last F π (λ i φ s d →
                                            k i φ s (inl (d , plug G c r))) f)
prev (F ⊚ G) π k (some (c , d))    r = plusMaybe
                                         (prev F all (λ m _ s c′ →
                                            first G π (λ i φ t d′ →
                                              k i φ t (some (c′ , d′))) s)
                                            c (plug G d r))
                                         (prev G π (λ i φ s d′ →
                                            k i φ s (some (c , d′))) d r)
prev (! o′)  π k c                 r = nothing
prev (Σ f)  π k (some {i′} c)     r = prev (f i′) π (λ i φ s d →
                                         k i φ s (some d)) c r
prev {J} {O} {r} {P} {o} {R}
     (Fix F) π k c                 s = prev F (onlyInl π) f c s
  where
    f : (i : (J + O)) → OnlyInl P i →
        (r ∣ μ F r) i → Ctx F i (r ∣ μ F r) o → Maybe R
    f (inr _) () r c
    f (inl i) φ  r c = k i φ r c
-}
-- stack of contexts
data Ctxs {I O : Set} (F : Code (I + O) O) (i : O) : I ▷ O where
  empty : {r : Indexed I} → Ctxs F i r i
  push  : {r : Indexed I} {m o : O} →
          Ctx F (inr i) (r ∣ μ F r) m → Ctxs F m r o → Ctxs F i r o

data Loc {I O : Set} (F : Code (I + O) O) : I ▷ O where
  loc : {r : Indexed I} {i o : O} →
        ⟦ Fix F ⟧ r i → Ctxs F i r o → Loc F r o

Nav : Set
Nav = {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O} →
      Loc F r o → Maybe (Loc F r o)

down : Nav
down {J} {O} {F} {r} {o}
     (loc {i = i′} ⟨ x ⟩ cs) = first F (onlyInr all) f x
  where
    f : (i : J + O) → OnlyInr All i → (r ∣ μ F r) i →
        Ctx F i (r ∣ μ F r) i′ → Maybe (Loc F r o)
    f (inl i) () r d
    f (inr i) tt r d = just (loc r (push d cs))

up : Nav
up (loc x empty)       = nothing
up {J} {O} {F} {r} {o}
   (loc x (push c cs)) = just (loc ⟨ plug F c x ⟩ cs)

right : Nav
right (loc x empty)               = nothing
right {J} {O} {F} {r} {o}
      (loc x (push {m = m} c cs)) = next F (onlyInr all) f c x
  where
    f : (i : J + O) → OnlyInr All i → (r ∣ μ F r) i →
        Ctx F i (r ∣ μ F r) m → Maybe (Loc F r o)
    f (inl i) () r d
    f (inr i) tt r d = just (loc r (push d cs))

left : Nav
left = up >=> down

enter : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
   →  ⟦ Fix F ⟧ r o → Loc F r o
enter x = loc x empty

-- doesn't pass termination checker (Ctxs should be a Vec)
leave : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
      → Loc F r o → ⟦ Fix F ⟧ r o
leave (loc x empty) = x
leave (loc x (push h t)) with (up (loc x (push h t)))
leave (loc x (push h t)) | nothing = leave (loc x (push h t)) -- impossible
leave (loc x (push h t)) | just p  = leave p

update : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
       → (∀ {i} → ⟦ Fix F ⟧ r i → ⟦ Fix F ⟧ r i) → Loc F r o → Loc F r o
update f (loc x l) = loc (f x) l

on : {A I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
   → (∀ {i} → (⟦ Fix F ⟧ r i) → A) → Loc F r o → A
on f (loc x _) = f x
