{-# OPTIONS --no-termination-check #-}

module Zipper where

open import Prelude hiding (up)
open import IxFun

-- Codes for contexts; would be nice if we could produce a Code again

mutual
  data Ctxs {I O : Set} (F : (I + O) ▸ O) (i : O) (r : Indexed I) : Indexed O where
    empty : Ctxs F i r i
    push  : {m o : O} → Ctx F (inr i) (r ∣ μ F r) m → Ctxs F m r o → Ctxs F i r o

  Ctx : {I O : Set} → I ▸ O → I → I ▷ O
  Ctx Z        i r o = ⊥
  Ctx U        i r o = ⊥
  Ctx (I i′)   i r o = i ≡ i′
  Ctx (F ↗ f ↘ g) i r o = ∃ (λ i′ → (f i′ ≡ i) × ∃ (λ o′ → (g o ≡ o′) × Ctx F i′ (r ∘ f) o′))
  Ctx (F ⊕ G)  i r o = Ctx F i r o + Ctx G i r o
  Ctx (F ⊗ G)  i r o = (Ctx F i r o × ⟦ G ⟧ r o) + (⟦ F ⟧ r o × Ctx G i r o)
  Ctx (F ⊚ G)  i r o = ∃ (λ m → Ctx F m (⟦ G ⟧ r) o × Ctx G i r m) 
  Ctx (! o′)   i r o = ⊥
  Ctx (Σ f)   i r o = ∃ (λ i′ → Ctx (f i′) i r o)
  Ctx (Fix F)  i r o = ∃ (λ m → Ctx F (inl i) (r ∣ μ F r) m × Ctxs F m r o)
  Ctx (Iso C D e) i r o = Ctx C i r o

-- plugging a value into a context
plug : {I O : Set} {r : Indexed I} {i : I} {o : O} →
       (C : I ▸ O) → Ctx C i r o → r i → ⟦ C ⟧ r o
plug Z       ()                r
plug U       ()                r
plug (I i)   refl              r = r
plug (F ↗ f ↘ g) (some (refl , some (refl , c))) r = plug F c r
plug (F ⊕ G) (inl c)           r = inl (plug F c r)
plug (F ⊕ G) (inr c)           r = inr (plug G c r)
plug (F ⊗ G) (inl (c , g))     r = plug F c r , g
plug (F ⊗ G) (inr (f , c))     r = f , plug G c r
plug (F ⊚ G) (some (c , d))    r = plug F c (plug G d r)
plug (! o)   ()                r
plug (Σ f)  (some {i} c)       r = some (plug (f i) c r)
plug {r = s} {o = o} (Fix F) (some {m} (c , cs)) r = unwrap m cs ⟨ plug F c r ⟩
  where
    unwrap : ∀ m → Ctxs F m s o → ⟦ Fix F ⟧ s m → ⟦ Fix F ⟧ s o
    unwrap .o empty           x = x
    unwrap m  (push {o} c cs) x = unwrap o cs ⟨ plug F c x ⟩
plug {r = s} {o = o} (Iso C D e) x r with e s o
plug {o = o} (Iso C D e) x r | ep = _≃_.to ep (plug C x r)


-- The function first takes a functor and splits it (CPS-style) into a
-- value and a context. Splitting can, in general, occur at any (input-)index. We
-- pass a predicate P that describes the indices we want to accept for
-- splitting.



mutual
  first : {I O : Set} {r : Indexed I} {o : O} {R : Set} →
          (C : I ▸ O) →
          ((i : I) → r i → Ctx C i r o → Maybe R) →
          ⟦ C ⟧ r o → Maybe R
  first Z       k ()
  first U       k x              = nothing
  first (I i)   k x              = k i x refl
  first (F ↗ f ↘ g) k x          = first F (λ i r c →
                                       k (f i) r (some (refl , some (refl , c)))) x
  first (F ⊕ G) k (inl x)        = first F (λ i r c →
                                       k i r (inl c)) x
  first (F ⊕ G) k (inr x)        = first G (λ i r c →
                                       k i r (inr c)) x
  first (F ⊗ G) k (x , y)        = plusMaybe
                                       (first F (λ i r c →
                                          k i r (inl (c , y))) x)
                                       (first G (λ i r c →
                                          k i r (inr (x , c))) y)
  first (F ⊚ G) k x              = first F (λ m s c →
                                       first G (λ i r d →
                                         k i r (some (c , d))) s) x
  first (! o)   k x              = nothing
  first (Σ f)  k (some {i′} y)   = first (f i′) (λ i r c →
                                       k i r (some c)) y

  first {J} {O} {r} {o} {R}
        (Fix F) k x              = firstFix F x empty k


  first {r = r} {o = o} (Iso C D e) k x with e r o
  first (Iso C D e) k x | ep = first C k (_≃_.from ep x)

  firstFix : {I O : Set} {r : Indexed I} {o : O} {R : Set} →
             {m : O} → (F : (I + O) ▸ O) →
             μ F r m → Ctxs F m r o →
             ((i : I) → r i → Ctx (Fix F) i r o → Maybe R) →
             Maybe R
  firstFix {J} {O} {r} {o} {R} {m} F ⟨ x ⟩ cs k = first F (contFix cs) x
    where
        contFix : {m : O} → Ctxs F m r o → (i : J + O) →
                  (r ∣ μ F r) i → Ctx F i (r ∣ μ F r) m → Maybe R
        contFix cs (inl i) r c = k i r (some (c , cs))
        contFix cs (inr i) r c = firstFix F r (push c cs) k


next : {I O : Set} {r : Indexed I} {o : O} {R : Set} →
       (C : I ▸ O) →
       ((i : I) → r i → Ctx C i r o → Maybe R) → 
       {i : I} → Ctx C i r o → r i → Maybe R
next Z       k ()                r
next U       k ()                r
next (I i)   k c                 r = nothing
next (F ↗ f ↘ g) k (some (refl , some (q , c))) r 
                                  = next F (λ i s d → 
                                         k (f i) s (some (refl , some (q , d)))) c r
next (F ⊕ G) k (inl c)           r = next F (λ i s d →
                                         k i s (inl d)) c r
next (F ⊕ G) k (inr c)           r = next G (λ i s d →
                                         k i s (inr d)) c r
next (F ⊗ G) k (inl (c , g))     r = plusMaybe
                                         (next F (λ i s d →
                                            k i s (inl (d , g))) c r)
                                         (first G (λ i s d →
                                            k i s (inr (plug F c r , d))) g)
next (F ⊗ G) k (inr (f , c))     r = next G (λ i s y →
                                         k i s (inr (f , y))) c r
next (F ⊚ G) k (some (c , d))    r = plusMaybe
                                         (next G (λ i s d′ →
                                            k i s (some (c , d′))) d r)
                                         (next F (λ m s c′ →
                                            first G (λ i t d′ →
                                              k i t (some (c′ , d′))) s)
                                            c (plug G d r))
next (! o′)  k c                 r = nothing
next (Σ f)  k (some {i′} c)      r = next (f i′) (λ i s d →
                                         k i s (some d)) c r
next {J} {O} {s} {o} {R}
     (Fix F) k (some {i′} (c , cs)) r = next F contFix c r
  where
    contFix : (i : J + O) → (s ∣ μ F s) i → Ctx F i (s ∣ μ F s) i′ → Maybe R
    contFix (inl i) r c = k i r (some (c , cs))
    contFix (inr i) r c = firstFix F r (push c cs) k

next (Iso C D e) k x s = next C k x s


data Loc {I O : Set} (F : (I + O) ▸ O) (r : Indexed I) (o : O) : Set where
  loc : {i : O} → ⟦ Fix F ⟧ r i → Ctxs F i r o → Loc F r o

Nav : Set₁
Nav = {I O : Set} {F : (I + O) ▸ O} {r : Indexed I} {o : O} →
      Loc F r o → Maybe (Loc F r o)

down : Nav
down {J} {O} {F} {r} {o}
     (loc {i = i′} ⟨ x ⟩ cs) = first F f x
  where
    f : (i : J + O) → (r ∣ μ F r) i →
        Ctx F i (r ∣ μ F r) i′ → Maybe (Loc F r o)
    f (inl i) r d = nothing
    f (inr i) r d = just (loc r (push d cs))

up : Nav
up (loc x empty)       = nothing
up {J} {O} {F} {r} {o}
   (loc x (push c cs)) = just (loc ⟨ plug F c x ⟩ cs)

right : Nav
right (loc x empty)               = nothing
right {J} {O} {F} {r} {o}
      (loc x (push {m = m} c cs)) = next F f c x
  where
    f : (i : J + O) → (r ∣ μ F r) i →
        Ctx F i (r ∣ μ F r) m → Maybe (Loc F r o)
    f (inl i) r d = nothing
    f (inr i) r d = just (loc r (push d cs))

left : Nav
left = up >=> down

enter : {I O : Set} {F : (I + O) ▸ O} {r : Indexed I} {o : O}
   →  ⟦ Fix F ⟧ r o → Loc F r o
enter x = loc x empty

enterEP : {I O : Set} {r : Indexed I} {o : O} {F : (I + O) ▸ O} {D : I ▷ O}
        → (e : (s : Indexed I) → (m : O) → D s m ≃ ⟦ Fix F ⟧ s m)
        → ⟦ Iso (Fix F) D e ⟧ r o → Loc F r o
enterEP {r = r} {o = o} e x with e r o
enterEP _ x | ep = enter (_≃_.from ep x)

-- Ctxs should be a Vec, and then we would not need a Maybe in the return type
leave : {I O : Set} {F : (I + O) ▸ O} {r : Indexed I} {o : O}
      → Loc F r o → Maybe (⟦ Fix F ⟧ r o)
leave (loc x empty) = just x
leave (loc x (push h t)) = up (loc x (push h t)) >>= leave

leaveEP : {I O : Set} {F : (I + O) ▸ O} {r : Indexed I} {o : O} {D : I ▷ O}
        → (e : (s : Indexed I) → (m : O) → D s m ≃ ⟦ Fix F ⟧ s m)
        → Loc F r o → Maybe (⟦ Iso (Fix F) D e ⟧ r o)
leaveEP {r = r} {o = o} e l with e r o
leaveEP _ l | ep = leave l >>= λ x → just (_≃_.to ep x)

update : {I O : Set} {F : (I + O) ▸ O} {r : Indexed I}
       → (⟦ Fix F ⟧ r ⇉ ⟦ Fix F ⟧ r) → Loc F r ⇉ Loc F r
update f _ (loc x l) = loc (f _ x) l

on : {I O : Set} {F : (I + O) ▸ O} {r : Indexed I} {o : O} {A : Indexed O}
   → (⟦ Fix F ⟧ r ⇉ A) → Loc F r o → ∃ A
on f (loc x _) = some (f _ x)
