{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Data.List where

import Universe
import Map


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
data Const a b = C { unC :: a }

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
