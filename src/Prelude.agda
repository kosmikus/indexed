{-# OPTIONS --universe-polymorphism #-}

module Prelude where

-- Universe polymorphism
data Level : Set where
  zero : Level
  suc  : Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

max : Level -> Level -> Level
max  zero    m      = m
max (suc n)  zero   = suc n
max (suc n) (suc m) = suc (max n m)

{-# BUILTIN LEVELMAX max #-}

----------------------------------------------------------------------
-- Trivial functions
----------------------------------------------------------------------

id : {A : Set} → A → A
id x = x

const : {A B : Set} → A → B → A
const x y = x


infixr 7 _∘_ 
-- Most general composition
_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
(f ∘ g) x = f (g x)

infixr 7 _⊙_ 
-- Composition without universe polymorphism
_⊙_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
(f ⊙ g) x = f (g x)

infixr 7 _∙_ 
-- Non-dependent composition
_∙_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∙ g) x = f (g x)

----------------------------------------------------------------------
-- Basic types and functions
----------------------------------------------------------------------

-- Empty type.
data ⊥ : Set where

-- Unit type.
data ⊤ : Set where
  tt : ⊤

-- Booleans
data Bool : Set where
  true  : Bool
  false : Bool

infixr 5 _∧_
infixr 4 _∨_

_∧_ : Bool → Bool → Bool
true ∧ true = true
_    ∧ _    = false

_∨_ : Bool → Bool → Bool
false ∨ false = false
_     ∨ _     = true

infixr 6 _×_
infixr 6 _,_

data _×_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (max ℓ₁ ℓ₂) where
  _,_ : A → B → A × B

fst : {ℓ : Level} {A B : Set ℓ} → A × B → A
fst (x , _) = x

snd : {ℓ : Level} {A B : Set ℓ} → A × B → B
snd (_ , y) = y

swap : {ℓ : Level} {A B : Set ℓ} → (A × B) → (B × A)
swap (x , y) = (y , x)

-- split operator

_▵_ : {I J R : Set} → (R → I) → (R → J) → R → (I × J)
(r ▵ s) x = r x , s x

infixr 5 _+_

-- Sum type.
data _+_ (A B : Set) : Set where 
  inl : A → A + B
  inr : B → A + B

-- junc operator
_▿_ : {I J R : Set} → (I → R) → (J → R) → (I + J) → R
(r ▿ s) (inl i) = r i
(r ▿ s) (inr j) = s j

_+++_ : {I J R S : Set} → (I → R) → (J → S) → (I + J) → (R + S)
_+++_ f g (inl i) = inl (f i)
_+++_ f g (inr j) = inr (g j)

flip : {I J : Set} → I + J → J + I
flip (inl i) = inr i
flip (inr j) = inl j

uncurry : {A B C : Set} → (A → B → C) → (A × B) → C
uncurry f (x , y) = f x y

-- equality type

infix 7 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

cong≡ : {a b : Level} {A : Set a} {B : Set b} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong≡ f refl = refl

cong≡₂ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → ∀ {x x′ y y′} 
       → (f : A → B → C) → x ≡ x′ → y ≡ y′ → f x y ≡ f x′ y′
cong≡₂ f refl refl = refl

trans≡ : {a : Level} → {A : Set a} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans≡ refl refl = refl

sym≡ : {a : Level} → {A : Set a} → {x y : A} → x ≡ y → y ≡ x
sym≡ refl = refl

subst≡ : {a : Level} → {A : Set a} → (P : A → Set a) → {x y : A} → x ≡ y → P x → P y
subst≡ P refl p = p

subst≡' : {x y : Set} → x ≡ y → x → y
subst≡' refl p = p

-- Negation

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

-- Decidable equality

data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

infix 7 _d≡_
_d≡_ : {ℓ : Level} {A : Set ℓ} → (x y : A) → Set ℓ
x d≡ y = Dec (x ≡ y)


-- existential

data ∃ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (B : A → Set ℓ₂) : Set (max ℓ₁ ℓ₂) where
  some : {x : A} → B x → ∃ B

data Maybe {a : Level} (A : Set a) : Set a where
  nothing : Maybe A
  just    : A → Maybe A

data Maybe₁ (A : Set₁) : Set₁ where
  nothing : Maybe₁ A
  just    : A → Maybe₁ A

mapMaybe : {a : Level} {A B : Set a} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing  = nothing
mapMaybe f (just x) = just (f x)

plusMaybe : {A : Set} → Maybe A → Maybe A → Maybe A
plusMaybe (just x) _ = just x
plusMaybe nothing  y = y

infixl 5 _>>=_
_>>=_ : ∀ {a} {A B : Set a} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= f = nothing
just x  >>= f = f x

infixl 6 _>=>_
_>=>_ : {A B C : Set} → (A -> Maybe B) -> (B -> Maybe C) -> A -> Maybe C
(f >=> g) x with f x
(f >=> g) x | nothing = nothing
(f >=> g) x | just y  = g y

-- Naturals
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

-- Fin
data Fin : Nat -> Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

finToNat : ∀ {n} → Fin n → Nat
finToNat zero    = zero
finToNat (suc n) = suc (finToNat n)

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_Nat+_ : Nat → Nat → Nat
zero  Nat+ n = n
suc m Nat+ n = suc (m Nat+ n)

{-# BUILTIN NATPLUS _Nat+_ #-}

_↑_ : ∀ {m} -> Fin m -> (n : Nat) -> Fin (n Nat+ m)
fn ↑ zero    = fn
fn ↑ (suc n) = suc (fn ↑ (n))

upTo : {n : Nat} → Fin (suc n)
upTo {zero}  = zero
upTo {suc n} = suc (upTo {n})

up : {m n : Nat} → m ≤ n → Fin m → Fin n
up .{0}    {0}     z≤n       f = f
up .{0}    {suc y} z≤n       f = upTo
up {suc m} {suc n} (s≤s m≤n) f = upTo
