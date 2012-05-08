{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Data.Bool where

import Universe

-------------------------------------------------------------------------------
-- Examples
-------------------------------------------------------------------------------

-- Booleans
type BoolF = (SUM UNIT UNIT :: Code Bot Top)

fromBool :: Bool -> Interprt BoolF r o
fromBool True = I_L I_U
fromBool False = I_R I_U

toBool :: Interprt BoolF r o -> Bool
toBool (I_L I_U) = True
toBool (I_R I_U) = False
