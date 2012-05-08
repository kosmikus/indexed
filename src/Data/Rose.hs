{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Data.Rose where

import Universe
import Map
import Data.List


-- Rose trees
data Rose a = Fork a [Rose a] deriving Show

type RoseF = (PROD (I (L TT)) (COMP List (I (R TT))) :: Code (Sum Top Top) Top)
type RoseC = (FIX RoseF :: Code Top Top)

data RoseI :: Top -> * where
  RoseI :: RoseI TT

-- This helped me visualise how rose trees look like
r1 :: Interprt RoseC (Const Int) TT
r1 = I_F (I_P (I_I (LL (C 0)))
              (I_C (I_F (I_R (I_P (I_I (LL (I_I (RR r1))))
                                  (I_I (RR (I_F (I_L I_U)))))))))


fromRose :: RoseI o -> Rose (r o) -> Interprt RoseC r o
fromRose RoseI (Fork a as) = I_F (I_P (I_I (LL a)) (I_C
                               (imap (I_I . RR . fromRose RoseI . unC) (fromList' as))))
                               -- I wonder if there's a way to use fromList here

fromRose' :: Rose a -> Interprt RoseC (Const a) TT
fromRose' (Fork a as) = I_F (I_P (I_I (LL (C a))) (I_C
                          (imap (I_I . RR . fromRose' . unC) (fromList' as))))
