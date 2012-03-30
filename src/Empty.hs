{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}

module Empty where

import Combinators
import Typelevel

class El p ix | ix -> p where
  proof :: p ix

class DecEq p where
  decEq :: El p ix => El p ix' => Maybe (ix :=: ix')

class Empty a where
  empty :: Bool -> a

class HEmpty pi po (f :: (* -> *) -> (* -> *)) | f -> pi, f -> po where
  hempty :: (forall ix. El pi ix => Bool -> r ix) -> El po ix => Bool -> f r ix

instance El pi ix => HEmpty pi po (I ix) where
  hempty f b = I (f b)

instance HEmpty pi po U where
  hempty f b = U

instance Empty a => HEmpty pi po (K a) where
  hempty f b = K (empty b)

instance (HEmpty pi po f, HEmpty pi po g) => HEmpty pi po (f :+: g) where
  hempty f True  = LL (hempty f True)
  hempty f False = RR (hempty f False)

instance (HEmpty pi po f, HEmpty pi po g) => HEmpty pi po (f :*: g) where
  hempty f b = hempty f b :*: hempty f b

instance (HEmpty (PEither pi po) po f) => HEmpty pi po (Fix f) where
  hempty f b = Fix (hempty (g proof) b)
    where
      g :: PEither pi po ix -> Bool -> (r :/: Fix f r) ix
      g (PLeft p)  b = JL (undefined)
      g (PRight _) b = JR (undefined)

{-
instance (HEmpty pi po f, HEmpty pi po g) => HEmpty pi po (f :.: g) where
  hempty f b = C (hempty (hempty f) b)
-}

instance (DecEq po, El po ix, HEmpty pi po f) => HEmpty pi po (Tag ix f) where
  hempty = hemptyTag 

hemptyTag :: forall pi po f r ix ix'. (HEmpty pi po f, DecEq po) => (forall ix. El pi ix => Bool -> r ix) -> El po ix => El po ix' => Bool -> Tag ix f r ix'
hemptyTag f b = case decEq :: Maybe (ix :=: ix') of Just Refl -> Tag (hempty f b)
                                                    Nothing   -> undefined
