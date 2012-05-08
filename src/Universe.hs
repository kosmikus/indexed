{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Universe where


-------------------------------------------------------------------------------
-- Indexing operators
-------------------------------------------------------------------------------

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
              | forall m. COMP (Code m o) (Code i m)
              | I i | O o
              | forall o'. X (o -> o') (Code i o')
              | forall i'. Y (i' -> i) (Code i' o)
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

-- So we use a data family instead. That seems to work.
data family Interprt (c :: Code i o) :: (i -> *) -> (o -> *)

data instance Interprt UNIT       r o = I_U
data instance Interprt (SUM a b)  r o = I_L (Interprt a r o)
                                      | I_R (Interprt b r o)
data instance Interprt (PROD a b) r o = I_P (Interprt a r o) (Interprt b r o)
data instance Interprt (COMP a b) r o = I_C { unI_C :: Interprt a (Interprt b r) o }
data instance Interprt (I i)      r o = I_I { unI_I :: r i }
data instance Interprt (O o')     r o where I_O :: Interprt (O o) r o

-- Output reindexing
data instance Interprt (X f a)    r o = I_X (Interprt a r (f o))

-- Input reindexing
newtype FunComp f g a = FunComp { unFunComp :: f (g a) }
data instance Interprt (Y g a)    r o = I_Y (Interprt a (FunComp r g) o)

data instance Interprt (FIX c)    r o where
  I_F :: Interprt c (Sum1 r (Interprt (FIX c) r)) o -> Interprt (FIX c) r o

{-
data instance Interprt (FIX c)    r o = I_F (Fix c r o)

data Fix :: Code (Sum i o) o -> (i -> *) -> o -> * where
  Mu :: Interprt c (Sum1 r (Fix c r)) o -> Fix c r o
-}

-------------------------------------------------------------------------------
-- Auxiliary
-------------------------------------------------------------------------------

data Bot
data Top = TT

data Proxy t = Proxy
