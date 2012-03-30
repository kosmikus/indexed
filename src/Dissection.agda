{-# OPTIONS --no-termination-check #-}

module Dissection where

open import Prelude hiding (up)
open import IxFun

-- Codes for contexts; would be nice if we could produce a Code again

-- "All-Left", could also be called "All-Clowns"
AL : {C J O : Set} → Code C O → (C + J) ▷ O
AL F r o = ⟦ F ⟧ (r ∘ inl) o

-- "All-Jokers", could also be called "All-Jokers"
AR : {C J O : Set} → Code J O → (C + J) ▷ O
AR F r o = ⟦ F ⟧ (r ∘ inr) o

rmap : {I O : Set} → Code I O → Indexed (I + I) → Indexed (O + O)
rmap F r = AL F r ∣ AR F r

mutual
{-
  -- recursive dissection structure
  data μDis {I O : Set}
            (F : Code (I + O) O)   -- functor with parameters and recursive input positions
            (i : I)
            (r : Indexed (I + I))
            (o : O)
            : Set where
    -- There's a hole of parameter i in the top-F-layer.
    inl : Dis F (inl i) ((r ∘ inl ∣ μ F (r ∘ inl)) ∣ (r ∘ inr ∣ μ F (r ∘ inr))) o → μDis F i r o
    -- We descend to the recursive Fix F-structure of index m, and in there continue.
    inr : {m : O} → Dis F (inr m) ((r ∘ inl ∣ μ F (r ∘ inl)) ∣ r ∘ inr ∣ μ F (r ∘ inr)) o → μDis F i r m → μDis F i r o
-}
  data Ctxs {I O : Set} (F : Code (I + O) O) (i : O) (r : Indexed (I + I)) : Indexed O where
    empty : Ctxs F i r i
    push  : {m o : O} → Dis F (inr i) ((r ∘ inl ∣ μ F (r ∘ inl)) ∣ r ∘ inr ∣ μ F (r ∘ inr)) m → Ctxs F m r o → Ctxs F i r o
  -- I think the definition of μDis above is bad (even if it is probably not wrong).
  -- We're interested in the actual hole, which is given by the inl constructor. Unfortunately,
  -- it is currently buried at the end of the structure. So, I think we should reverse
  -- the structure and represent a μDis as a pair of a Dis F (inl i) for a suitable i, plus
  -- a (possibly empty) stack of Dis F (inr m) for suitable ms.

  -- one-layer dissection structure:
  -- for ever input index, two slots are created (clowns, jokers)
  Dis : {I O : Set} → Code I O → I → (I + I) ▷ O
  Dis Z        i r o = ⊥
  Dis U        i r o = ⊥
--  Dis (K A)    i r o = ⊥
  Dis (I i′)   i r o = i ≡ i′
  Dis (X f F)  i r o = ∃ (λ o′ → (f o ≡ o′) × Dis F i  r             o′)
  Dis (Y f F)  i r o = ∃ (λ i′ → (f i′ ≡ i) × Dis F i′ (r ∘ f +++ f) o)
  Dis (F ⊕ G)  i r o = Dis F i r o + Dis G i r o
  -- The key difference compared to the zipper: We use different types
  -- for the occurrences to the left and to the right of the focus.
  Dis (F ⊗ G)  i r o = (Dis F i r o × AR G r o) + (AL F r o × Dis G i r o)
  Dis (F ⊚ G)  i r o = ∃ (λ m → Dis F m (AL G r ∣ AR G r) o × Dis G i r m) 
  Dis (! o′)   i r o = ⊥
  Dis (Σ f)   i r o = ∃ (λ i′ → Dis (f i′) i r o)
--  Dis (Fix F)  i r o = Ctxs F i r o
  Dis (Fix F)  i r o = ∃ (λ m → Dis F (inl i) ((r ∘ inl ∣ μ F (r ∘ inl)) ∣ (r ∘ inr ∣ μ F (r ∘ inr))) m × Ctxs F m r o)
  Dis (EP C D e) i r o = Dis C i r o

-- plugging a value into a context
plug : {I O : Set} {r : Indexed I} {i : I} {o : O} →
       (C : Code I O) → Dis C i (r ∣ r) o → r i → ⟦ C ⟧ r o
plug Z       ()                r
plug U       ()                r
--plug (K A)   ()                r
plug (I i)   refl              r = r
plug (X R F) (some (refl , c)) r = plug F c r
plug (Y f F) (some (refl , c)) r = plug F {!c!} r
plug (F ⊕ G) (inl c)           r = inl (plug F c r)
plug (F ⊕ G) (inr c)           r = inr (plug G c r)
plug (F ⊗ G) (inl (c , g))     r = plug F c r , g
plug (F ⊗ G) (inr (f , c))     r = f , plug G c r
plug (F ⊚ G) (some (c , d))    r = plug F c (plug G d r)
plug (! o)   ()                r
plug (Σ f)  (some {i} c)      r = some (plug (f i) c r)
{-
plug (Fix F) (inl c)           r = ⟨ plug F c r ⟩
plug (Fix F) (inr c d)         r = ⟨ plug F c (plug (Fix F) d r) ⟩
-}
plug {o = o} (Fix F) (some (c , cs)) r = unwrap cs ⟨ plug F c r ⟩ where
  unwrap : ∀ {m} → Ctxs F m _ o → ⟦ Fix F ⟧ _ m → ⟦ Fix F ⟧ _ o
  unwrap empty       x = x
  unwrap (push c cs) x = unwrap cs ⟨ plug F c x ⟩
plug {r = s} {o = o} (EP C D e) x r with e s o
plug {o = o} (EP C D e) x r | ep = _≃_.to ep (plug C x r)

p⊕F : {I C E : Set} {A B D : I → Set} → ∃ (λ i → A i × B i) + C → ∃ (λ i → A i × (B i + D i)) + (C + E)
p⊕F (inl (some (x , y))) = inl (some (x , inl y))
p⊕F (inr z)              = inr (inl z)

p⊕G : {I C E : Set} {A B D : I → Set} → ∃ (λ i → A i × B i) + C → ∃ (λ i → A i × (D i + B i)) + (E + C)
p⊕G (inl (some (x , y))) = inl (some (x , inr y))
p⊕G (inr z)              = inr (inr z)

mutual

  --  inl : Dis F (inl i) ((r ∘ inl ∣ μ F (r ∘ inl)) ∣ (r ∘ inr ∣ μ F (r ∘ inr))) o → μDis F i r o
  --  inl : Dis F (inl i) ((c ∣ μ F c) ∣ (j ∣ μ F j)) o → μDis F i (c ◆ j) o
{-
  rightFixs : {I O : Set} {c j : Indexed I} {o : O} {R : Set} →
              (F : Code (I + O) O) →
              ((i : I) → j i → μDis F i (c ∣ j) o → R) →
              (⟦ Fix F ⟧ c o → R) →
              (i : I + O) → (j ∣ μ F j) i → Dis F i ((c ∣ μ F c) ∣ (j ∣ μ F j)) o →
              R
  rightFixs F kc ke (inl i) x cx = kc i x (inl cx)
  rightFixs F kc ke (inr o) x cx = rights (Fix F)
                                          (λ i y cy → kc i y (inr cx cy))
                                          {!!}
                                          x
-}
  right⊚s : {I M O : Set} {c j : Indexed I} {o : O} {R : Set} →
            (F : Code M O) (G : Code I M) →
            ((m : M) → Dis F m (⟦ G ⟧ c ∣ ⟦ G ⟧ j) o → (i : I) → j i → Dis G i (c ∣ j) m → R) →
            (⟦ F ⊚ G ⟧ c o → R) →
            (m : M) → Dis F m (⟦ G ⟧ c ∣ ⟦ G ⟧ j) o → ⟦ G ⟧ j m → R
  right⊚s F G kc ke m cy x = rights G
                                 (kc m cy)
                                 (λ y → rightc F (λ m' y' cy' → right⊚s F G kc ke m' cy' y')
                                                 ke
                                                 m cy y)
                                 x

  right⊚c : {I M O : Set} {c j : Indexed I} {o : O} {R : Set} →
            (F : Code M O) (G : Code I M) →
            ((m : M) → Dis F m (⟦ G ⟧ c ∣ ⟦ G ⟧ j) o → (i : I) → j i → Dis G i (c ∣ j) m → R) →
            (⟦ F ⊚ G ⟧ c o → R) →
            (m : M) → Dis F m (⟦ G ⟧ c ∣ ⟦ G ⟧ j) o → (i : I) → Dis G i (c ∣ j) m → c i → R
  right⊚c F G kc ke m cy i cx x = rightc G
                                      (kc m cy)
                                      (λ y → rightc F (λ m' y' cy' → right⊚s F G kc ke m' cy' y')
                                                      ke
                                                      m cy y)
                                      i cx x


  -- Function that tries to move the focus gradually to the right, CPS.
  -- The direct-style version of this function has the following type:
  --
  -- (⟦ C ⟧ j o + ∃ (λ i → Dis C i (c ∣ j) o × c i)) →
  -- ∃ (λ i → (j i × Dis C i (c ∣ j) o)) + ⟦ C ⟧ c o
  --
  -- The CPS version consists of two functions for the two cases:
  --
  -- rights just takes the ⟦ C ⟧ j o (situation where we're in the left),
  -- whereas
  -- rightc takes the dissection and a single clown
  --
  -- the results are represented by two continuations
  --
  -- note that other than the "right" function we usually implement for
  -- zippers, Conor's version of "right" actually performs an inorder
  -- traversal of all the nodes

  rights : {I O : Set} {c j : Indexed I} {o : O} {R : Set} →
           (C : Code I O) →
           ((i : I) → j i → Dis C i (c ∣ j) o → R) →
           (⟦ C ⟧ c o → R) →
           ⟦ C ⟧ j o → R
  rights Z       kc ke ()

  -- 'U' represents a constant, and a constant has no slots for potential holes,
  -- so we jump over it in one go
  rights U       kc ke tt      = ke tt

  -- 'I' represents a recursive position which can be "entered", which we do
  rights (I i)   kc ke x       = kc i x refl

  -- In order to enter a sum, we have to enter the component that is actually
  -- given to us. The continuations just need to be adapted.
  rights (F ⊕ G) kc ke (inl x) = rights F (λ i y cy → kc i y (inl cy))
                                          (λ y → ke (inl y)) x
  rights (F ⊕ G) kc ke (inr x) = rights G (λ i y cy → kc i y (inr cy))
                                          (λ y → ke (inr y)) x

  -- In order to enter a pair, we try to enter the left component. If that
  -- fails, we have to try to enter the right component instead.
  rights (F ⊗ G) kc ke (x , y) = rights F (λ i z cz → kc i z (inl (cz , y)))
                                          (λ x' → rights G (λ i z cz → kc i z (inr (x' , cz)))
                                                           (λ z → ke (x' , z)) y) x

  -- Entering a composition starts with entering the F-structure. If we
  -- succeed, we try to enter a G-structure inside; if we can't find a G-structure
  -- in the F-structure, we have to try the next F-structure repeatedly until we
  -- finally find a G-structure. This is the job of right⊚s.
  rights (F ⊚ G) kc ke x       = rights F (λ i y cy →
                                           right⊚s F G
                                                   (λ m cy' i' z cz → kc i' z (some (cy' , cz)))
                                                   ke
                                                   _ cy y)
                                        ke x

  -- Entering a fixed point:
  -- We unfold the top-layer and thus have an F-structure with as children
  -- either parameters or Fix F-structures again. We look for the first hole
  -- within the F-structure. If it's a parameter, then fine. Otherwise, it's
  -- a Fix F-structure, and we have to repeat the process. In principle, we
  -- can obtain many layers of F-structures we're traversing, and need a form
  -- of stack to maintain the state.
{-
  rights {J} {O} {c} {j} {o} {R} (Fix F) kc ke ⟨ x ⟩ = rights F kc' (λ y → ke ⟨ y ⟩) x
    where kc' : (i : J + O) → (j ∣ μ F j) i → Dis F i ((c ∣ μ F c) ∣ (j ∣ μ F j)) o → R
          kc' (inl i) y cy = kc i y (inl cy)
          kc' (inr i) y cy = rights (Fix F) (λ k z cz → kc k z (inr cy cz)) (λ z → {!!}) y
-}
  rights {J} {O} {c} {j} {o} {R} (Fix F) kc ke x = rightsFix x empty where
    rightsFix : {m : O} → μ F j m → Ctxs F m _ o → R
    rightsFix {m} ⟨ x ⟩ cs = rights F kcFix (keFix cs) x where
      kcFix : (i : J + O) → (j ∣ μ F j) i → Dis F i _ m → R
      kcFix (inl i) y z = kc i y (some (z , cs))
      kcFix (inr i) y z = rightsFix y (push z cs)
      keFix : {n : O} → Ctxs F n _ o → ⟦ F ⟧ _ n → R
      keFix     empty       y = ke ⟨ y ⟩
      keFix {n} (push d ds) y = {!!}

{-
  rights (Fix F) kc ke ⟨ x ⟩   = rights F (λ i y cy → rightFixs F kc ke i y cy)
                                       (λ y → ke ⟨ y ⟩) x
-}

  rights C kc ke p  = {!!}


  rightc : {I O : Set} {c j : Indexed I} {o : O} {R : Set} →
           (C : Code I O) →
           ((i : I) → j i → Dis C i (c ∣ j) o → R) →
           (⟦ C ⟧ c o → R) →
           (i : I) → Dis C i (c ∣ j) o → c i → R
  rightc Z       kc ke _  ()       x

  -- constants have no slots for potential holes, so the situation that we are
  -- in the middle of a constant is impossible
  rightc U       kc ke _  ()       x

  -- if we are in a recursive position, we leave it immediately
  rightc (I i)   kc ke .i refl     x = ke x

  -- In order to move through a sum, we move in the component that is
  -- actually given to us and adapt the continuations.
  rightc (F ⊕ G) kc ke _  (inl cx) x = rightc F (λ i y cy → kc i y (inl cy))
                                                (λ y → ke (inl y)) _ cx x
  rightc (F ⊕ G) kc ke _  (inr cx) x = rightc G (λ i y cy → kc i y (inr cy))
                                                (λ y → ke (inr y)) _ cx x

  -- Moving through a pair is trickier if we're still in the left part,
  -- because then we have to try moving into the right if we get to the
  -- end of the left.
  rightc (F ⊗ G) kc ke _  (inl (cx , y)) x = rightc F (λ i z cz → kc i z (inl (cz , y)))
                                                      (λ x' → rights G (λ i z cz → kc i z (inr (x' , cz)))
                                                                       (λ z → ke (x' , z)) y) _ cx x
  rightc (F ⊗ G) kc ke _  (inr (x , cy)) y = rightc G (λ i z cz → kc i z (inr (x , cz)))
                                                      (λ z → ke (x , z)) _ cy y

  -- We have to move right in the G-structure, but move the F-structure
  -- along if we don't find another G-structure.
  rightc (F ⊚ G) kc ke _  (some (cx , cy)) y = right⊚c F G
                                                       (λ m cy' i' z cz → kc i' z (some (cy' , cz)))
                                                       ke
                                                       _ cx _ cy y
  -- Moving through a fixed point.
  -- The current state is given by a list of F-structures we're currently traversing.

{-

  rightc (Fix F) kc ke i (inl cx)     x = rightc F (λ i' y cy → rightFixs F kc ke i' y cy)
                                                   (λ y → ke ⟨ y ⟩)
                                                   (inl i) cx x
  rightc (Fix F) kc ke i (inr cx cys) x = rightc F {!!} {!!} {!!} {!!} {!!}

  rightc C       kc ke i  cp p = {!!}
-}
{-
  rightc {J} {O} {c} {j} {o} {R} (Fix F) kc ke i (inl x) z = rightc F kc' (λ y → ke ⟨ y ⟩) (inl i) x z
    where kc' : (i' : J + O) → ((λ {x} → c ∣ j) ∘ inr ∣ μ F ((λ {x} → c ∣ j) ∘ inr)) i'
              → Dis F i' ((c ∣ μ F c) ∣ (λ {x} → c ∣ j) ∘ inr ∣ μ F ((λ {x} → c ∣ j) ∘ inr)) o → R
          kc' (inl i') y cy = kc i' y (inl cy)
          kc' (inr i') y cy = rights (Fix F) (λ j' z' cz → kc j' z' (inr cy cz)) (λ z' → {!!}) y
  rightc (Fix F) kc ke i (inr x y) z = rightc (Fix F) (λ j z' cz → kc j z' (inr x cz)) (λ z' → {!!}) i y z
-}

  rightc {J} {O} {c} {j} {o} {R} (Fix F) kc ke i (some {.o} (x , empty)) z =
    rightc F kc' (λ y → ke ⟨ y ⟩) (inl i) x z where
      kc' : (k : J + O) → ((c ∣ j) ∘ inr ∣ μ F ((c ∣ j) ∘ inr)) k → Dis F k _ o → R
      kc' (inl k) jk y = kc k jk (some (y , empty))
      kc' (inr k) jk y = {!!}
  rightc {J} {O} {c} {j} {o} {R} (Fix F) kc ke i (some {n} (x , push d ds)) z =
    rightc (Fix F) kc' ke i (some ({!x!} , ds)) z where
      kc' : (k : J) → j k → ∃ (λ m → Dis F (inl k) _ m × Ctxs F m _ o) → R
      kc' k jk (some {m} (y , ys)) = kc k jk (some (y , push {!d!} ys))

  rightc C     kc ke i  cp p = {!!}

{-
right : {I O : Set} {c j : Indexed I} {o : O} →
       (C : Code I O) →
       (⟦ C ⟧ j o + ∃ (λ i → Dis C i (c ∣ j) o × c i)) →
       ∃ (λ i → (j i × Dis C i (c ∣ j) o)) + ⟦ C ⟧ c o
right Z p with p
right Z p | inl ()
right Z p | inr (some (() , _))
right U p with p
right U p | inl tt = inr tt
right U p | inr (some (() , _))
right (F ⊕ G) p with p
right (F ⊕ G) p | inl (inl x)            = p⊕F (right F (inl x))
right (F ⊕ G) p | inl (inr x)            = p⊕G (right G (inl x))
right (F ⊕ G) p | inr (some (inl x , c)) = p⊕F (right F (inr (some (x , c))))
right (F ⊕ G) p | inr (some (inr x , c)) = p⊕G (right G (inr (some (x , c))))
right (F ⊗ G) p with p
right (F ⊗ G) p | inl (y , y') = {!!}
right (F ⊗ G) p | inr (some (inl (y , y') , y0)) = {!!}
right (F ⊗ G) p | inr (some (inr (y , y') , y0)) = {!!}
right _ _ = {!!}
-}
{-
right (I i′) f i with f i
right (I i′) f i   | inl x = inl ({!!} , {!!})
right (I i′) f .i′ | inr (refl , c) = inr c
right (F ⊕ G) f i | inl (inl y) = {!!}
right (F ⊕ G) f i | inl (inr y) = {!!}
right (F ⊕ G) f i | inr x = {!!}
right _ _ _ = {!!}
-}


{-
-- The function first takes a functor and splits it (CPS-style) into a
-- value and a context. Splitting can, in general, occur at any (input-)index. We
-- pass a predicate P that describes the indices we want to accept for
-- splitting.


first : {I O : Set} {r : Indexed I} {o : O} {R : Set} →
        (C : Code I O) →
        ((i : I) → r i → Dis C i r o → Maybe R) → 
        ⟦ C ⟧ r o → Maybe R
first Z       k ()
first U       k x              = nothing
--first (K A)   k x              = nothing
first (I i)   k x              = k i x refl
first (X R F) k x              = first F (λ i r c →
                                     k i r (some (refl , c))) x
first (Y f F) k x              = first F (λ i′ y c →
                                     k (f i′) y (some (refl , c))) x
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
first (Σ f)  k (some {i′} y)  = first (f i′) (λ i r c →
                                       k i r (some c)) y

first {J} {O} {r} {o} {R}
      (Fix F) k ⟨ x ⟩          = first F f x
  where
    f : (i : (J + O)) →
        (r ∣ μ F r) i → Dis F i (r ∣ μ F r) o → Maybe R
    f (inl j) r c = k j r (inl c)
    f (inr j) r c = first (Fix F) (λ i s d → k i s (inr c d)) r

first {r = r} {o = o} (EP C D e) k x with e r o 
first (EP C D e) k x | ep = first C k (_≃_.from ep x)


next : {I O : Set} {r : Indexed I} {o : O} {R : Set} →
       (C : Code I O) →
       ((i : I) → r i → Dis C i r o → Maybe R) → 
       {i : I} → Dis C i r o → r i → Maybe R
next Z       k ()                r
next U       k ()                r
-- next (K A)   k ()                r
next (I i)   k c                 r = nothing
next (X R F) k (some (p , c))    r = next F (λ i s d →
                                         k i s (some (p , d))) c r
next (Y f F) k (some (refl , c)) r = next F (λ i′ s d →
                                         k (f i′) s (some (refl , d))) c r
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
next (Σ f)  k (some {i′} c)     r = next (f i′) (λ i s d →
                                         k i s (some d)) c r
next {J} {O} {r} {o} {R}
     (Fix F) k (inl c′)          s = next F f c′ s
  where
    f : (i : (J + O)) →
        (r ∣ μ F r) i → Dis F i (r ∣ μ F r) o → Maybe R
    f (inl j) r c = k j r (inl c)
    f (inr j) r c = first (Fix F) (λ i s d → k i s (inr c d)) r
next {J} {O} {r} {o} {R}
     (Fix F) k (inr c′ d′)       s = plusMaybe
                                       (next (Fix F) (λ i s d → k i s (inr c′ d)) d′ s)
                                       (next F f c′ (plug (Fix F) d′ s))
  where
    f : (i : (J + O)) →
        (r ∣ μ F r) i → Dis F i (r ∣ μ F r) o → Maybe R
    f (inl j) r c = k j r (inl c)
    f (inr j) r c = first (Fix F) (λ i s d → k i s (inr c d)) r

next (EP C D e) k x s = next C k x s


-- stack of contexts
data Diss {I O : Set} (F : Code (I + O) O) (i : O) (r : Indexed I) : Indexed O where
  empty : Diss F i r i
  push  : {o m : O} → Dis F (inr i) (r ∣ μ F r) m → Diss F m r o → Diss F i r o

data Loc {I O : Set} (F : Code (I + O) O) (r : Indexed I) (o : O) : Set where
  loc : {i : O} → ⟦ Fix F ⟧ r i → Diss F i r o → Loc F r o

Nav : Set₁
Nav = {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O} →
      Loc F r o → Maybe (Loc F r o)

down : Nav
down {J} {O} {F} {r} {o}
     (loc {i = i′} ⟨ x ⟩ cs) = first F f x
  where
    f : (i : J + O) → (r ∣ μ F r) i →
        Dis F i (r ∣ μ F r) i′ → Maybe (Loc F r o)
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
        Dis F i (r ∣ μ F r) m → Maybe (Loc F r o)
    f (inl i) r d = nothing
    f (inr i) r d = just (loc r (push d cs))

left : Nav
left = up >=> down
{-
data Diss {I O : Set} (F : Code (I + O) O) (i : O) : I ▷ O where
  empty : {r : Indexed I} → Diss F i r i
  push  : {r : Indexed I} {m o : O} → 
          Dis F (inr i) (r ∣ μ F r) m → Diss F m r o → Diss F i r o

data Loc {I O : Set} (F : Code (I + O) O) : I ▷ O where
  loc : {r : Indexed I} {i o : O} →
        ⟦ Fix F ⟧ r i → Diss F i r o → Loc F r o

Nav : Set
Nav = {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O} →
      Loc F r o → Maybe (Loc F r o)

down : Nav
down {J} {O} {F} {r} {o}
     (loc {i = i′} ⟨ x ⟩ cs) = first F f x
  where
    f : (i : J + O) → OnlyInr All i → (r ∣ μ F r) i →
        Dis F i (r ∣ μ F r) i′ → Maybe (Loc F r o)
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
        Dis F i (r ∣ μ F r) m → Maybe (Loc F r o)
    f (inl i) () r d
    f (inr i) tt r d = just (loc r (push d cs))

left : Nav
left = up >=> down
-}
enter : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
   →  ⟦ Fix F ⟧ r o → Loc F r o
enter x = loc x empty

enterEP : {I O : Set} {r : Indexed I} {o : O} {F : Code (I + O) O} {D : I ▷ O}
        → (e : (s : Indexed I) → (m : O) → D s m ≃ ⟦ Fix F ⟧ s m)
        → ⟦ EP (Fix F) D e ⟧ r o → Loc F r o
enterEP {r = r} {o = o} e x with e r o
enterEP _ x | ep = enter (_≃_.from ep x)

-- Diss should be a Vec, and then we would not need a Maybe in the return type
leave : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O}
      → Loc F r o → Maybe (⟦ Fix F ⟧ r o)
leave (loc x empty) = just x
leave (loc x (push h t)) = up (loc x (push h t)) >>= leave
{-
leave (loc x (push h t)) | nothing = leave (loc x (push h t)) -- impossible
leave (loc x (push h t)) | just p  = leave p
-}
leaveEP : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O} {D : I ▷ O}
        → (e : (s : Indexed I) → (m : O) → D s m ≃ ⟦ Fix F ⟧ s m)
        → Loc F r o → Maybe (⟦ EP (Fix F) D e ⟧ r o)
leaveEP {r = r} {o = o} e l with e r o
leaveEP _ l | ep = leave l >>= λ x → just (_≃_.to ep x)

update : {I O : Set} {F : Code (I + O) O} {r : Indexed I}
       → (⟦ Fix F ⟧ r ⇉ ⟦ Fix F ⟧ r) → Loc F r ⇉ Loc F r
update f _ (loc x l) = loc (f _ x) l

on : {I O : Set} {F : Code (I + O) O} {r : Indexed I} {o : O} {A : Indexed O}
   → (⟦ Fix F ⟧ r ⇉ A) → Loc F r o → ∃ A
on f (loc x _) = some (f _ x)

-}
