{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Map where

import Universe

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

instance (IMap a) => IMap (X f a) where
  imap f (I_X a) = I_X (imap f a)

instance (IMap a) => IMap (Y g a) where
  imap f (I_Y a) = I_Y (imap (FunComp . f . unFunComp) a)

instance (IMap c) => IMap (FIX c) where
  imap f (I_F x) = I_F (imap (f // imap f) x)

-------------------------------------------------------------------------------
-- Recursion schemes
-------------------------------------------------------------------------------

cata :: IMap c => (Interprt c (Sum1 r s) :->: s) -> (Interprt (FIX c) r :->: s)
cata phi (I_F x) = phi (imap (id // cata phi) x)

ana  :: IMap c => (s :->: Interprt c (Sum1 r s)) -> (s :->: Interprt (FIX c) r)
ana psi x = I_F (imap (id // ana psi) (psi x))

hylo :: IMap c => (Interprt c (Sum1 r t) :->: t) -> (s :->: Interprt c (Sum1 r s)) -> (s :->: t)
hylo phi psi x = phi (imap (id // hylo phi psi) (psi x))
