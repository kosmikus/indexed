{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Indexed where

infixr 7 :->:
type (r :->: s) = forall ix. r ix -> s ix

data Sum a b = L a | R b

data Sum1 (a :: i1 -> *) (b :: i2 -> *) :: Sum i1 i2 -> * where
  LL :: a i -> Sum1 a b (L i)
  RR :: b i -> Sum1 a b (R i)


(//) :: (r :->: r') -> (s :->: s')
     -> (Sum1 r s) :->: (Sum1 r' s')
(f // _) (LL x) = LL (f x)
(_ // g) (RR x) = RR (g x)

-------------------------------------------------------------------------------
-- Universe
-------------------------------------------------------------------------------
data Code i o = UNIT
              | SUM (Code i o) (Code i o)
              | PROD (Code i o) (Code i o)
              -- I thought existentials couldn't be promoted... O_o
              | forall m. COMP (Code m o) (Code i m)
              | I i | O o
              | FIX (Code (Sum i o) o)

-------------------------------------------------------------------------------
-- Interpretation 
-------------------------------------------------------------------------------
-- We cannot give the interpretation as a datatype.
-- I don't fully understand why, but if I transpose the code to Agda it
-- only compiles with --type-in-type...
--data Interprt (c :: Code i o) (r :: i -> *) (j :: o) where
{-
data Interprt :: Code i o -> (i -> *) -> o -> * where
  I_U :: Interprt UNIT r o
  I_L :: Interprt a r o -> Interprt (SUM a b) r o
  I_R :: Interprt b r o -> Interprt (SUM a b) r o
  I_P :: Interprt a r o -> Interprt b r o -> Interprt (PROD a b) r o
  I_I :: r i -> Interprt (I i) r o
  I_O :: Interprt (O o) r o
  I_F :: Fix c r o -> Interprt (FIX c) r o
--data Fix (c :: Code (Sum i o) o) (r :: i -> *) (j :: o) where
data Fix :: Code (Sum i o) o -> (i -> *) -> o -> * where
  Mu :: Interprt c (Sum1 r (Fix c r)) o -> Fix c r o
-}
-- So we use a data family. That seems to work.
data family Interprt (c :: Code i o) :: (i -> *) -> (o -> *)

data instance Interprt UNIT       r o = I_U
data instance Interprt (SUM a b)  r o = I_L (Interprt a r o)
                                      | I_R (Interprt b r o)
data instance Interprt (PROD a b) r o = I_P (Interprt a r o) (Interprt b r o)
data instance Interprt (COMP a b) r o = I_C (Interprt a (Interprt b r) o)
data instance Interprt (I i)      r o = I_I (r i)
data instance Interprt (O o')     r o where I_O :: Interprt (O o) r o
-- Then we also don't need an auxiliary datatype for the interpretation
-- of FIX:
data instance Interprt (FIX c)    r o where
  I_F :: Interprt c (Sum1 r (Interprt (FIX c) r)) o -> Interprt (FIX c) r o

{-
data instance Interprt (FIX c)    r o = I_F (Fix c r o)

data Fix :: Code (Sum i o) o -> (i -> *) -> o -> * where
  Mu :: Interprt c (Sum1 r (Fix c r)) o -> Fix c r o
-}

-------------------------------------------------------------------------------
-- Map 
-------------------------------------------------------------------------------

class IMap (c :: Code i' o') where
  imap :: (r :->: s) -> (Interprt c r :->: Interprt c s)

instance IMap UNIT where
  imap _ I_U = I_U

instance (IMap a, IMap b) => IMap (SUM a b) where
  imap f (I_L x) = I_L (imap f x)
  imap f (I_R x) = I_R (imap f x)

instance (IMap a, IMap b) => IMap (PROD a b) where
  imap f (I_P x y) = I_P (imap f x) (imap f y)

instance (IMap a, IMap b) => IMap (COMP a b) where
  imap f (I_C x) = I_C (imap (imap f) x)

instance IMap (I i) where
  imap f (I_I x) = I_I (f x)

instance IMap (O o) where
  imap f I_O = I_O

instance (IMap c) => IMap (FIX c) where
  imap f (I_F x) = I_F (imap (f // imap f) x)

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

data Bot
data Top = TT

-- Booleans
type BoolF = (SUM UNIT UNIT :: Code Bot Top)

fromBool :: Bool -> Interprt BoolF r o
fromBool True = I_L I_U
fromBool False = I_R I_U

toBool :: Interprt BoolF r o -> Bool
toBool (I_L I_U) = True
toBool (I_R I_U) = False

-- Peano style natural numbers
data Peano = Zero | Suc Peano

type NatF = (SUM UNIT (I (R TT)) :: Code (Sum Bot Top) Top)
type Nat = (FIX NatF :: Code Bot Top)

fromNat :: Peano -> Interprt Nat r o
fromNat Zero    = I_F (I_L I_U)
fromNat (Suc n) = I_F (I_R (I_I (RR (fromNat n))))

toNat :: Interprt Nat r o -> Peano
toNat (I_F (I_L I_U))          = Zero
toNat (I_F (I_R (I_I (RR n)))) = Suc (toNat n)

-- Lists
type ListF = (SUM UNIT (PROD (I (L TT)) (I (R TT))) :: Code (Sum Top Top) Top)
type List = (FIX ListF :: Code Top Top)

data ListIndex :: Top -> * where
  L_TT :: ListIndex TT

fromList :: ListIndex o -> [r o] -> Interprt List r o
fromList L_TT []     = I_F (I_L I_U)
fromList L_TT (x:xs) = I_F (I_R (I_P (I_I (LL x)) (I_I (RR (fromList L_TT xs)))))

toList :: ListIndex o -> Interprt List r o -> [r o]
toList L_TT (I_F (I_L I_U)) = []
toList L_TT (I_F (I_R (I_P (I_I (LL x)) (I_I (RR xs))))) = (x:toList L_TT xs)

-- Functorial mapping for lists
data Const a b = C a

fromList' :: [a] -> Interprt List (Const a) o
fromList' []     = I_F (I_L I_U)
fromList' (x:xs) = I_F (I_R (I_P (I_I (LL (C x))) (I_I (RR (fromList' xs)))))

toList' :: Interprt List (Const a) o -> [a]
toList' (I_F (I_L I_U)) = []
toList' (I_F (I_R (I_P (I_I (LL (C x))) (I_I (RR xs))))) = (x:toList' xs)

up :: (a -> b) -> (Const a :->: Const b)
up f (C x) = C (f x)

mapList :: (a -> b) -> [a] -> [b]
mapList f = toList' . imap (up f) . fromList'
