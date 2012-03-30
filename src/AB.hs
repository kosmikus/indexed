{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}

module AB where

import Combinators
import Typelevel
import EP

data A = AZero | ASucc B deriving (Show)
data B = BZero | BSucc A deriving (Show)

-- PFA, PFB :: Fin 0 + Fin 2 >>> o
type PFA = K () :+: (I (TRight (Succ Zero)))
type PFB = K () :+: (I (TRight (     Zero)))

-- PFAB :: Fin 0 >>> Fin 2
type PFAB = Fix (Tag Zero PFA :+: Tag (Succ Zero) PFB)

type PFAB' = PFAB Nil

fromA :: A -> PFAB' Zero
fromA AZero     = Fix (LL (Tag (LL (K ()))))
fromA (ASucc b) = Fix (LL (Tag (RR (I (JR (fromB b))))))

toA :: PFAB' Zero -> A
toA (Fix (LL (Tag (LL (K ())))))     = AZero
toA (Fix (LL (Tag (RR (I (JR b)))))) = ASucc (toB b)

fromB :: B -> PFAB' (Succ Zero)
fromB BZero     = Fix (RR (Tag (LL (K ()))))
fromB (BSucc a) = Fix (RR (Tag (RR (I (JR (fromA a))))))

toB :: PFAB' (Succ Zero) -> B
toB (Fix (RR (Tag (LL (K ())))))     = BZero
toB (Fix (RR (Tag (RR (I (JR a)))))) = BSucc (toA a)

fromAB' :: (Cons A (Cons B Nil)) ix -> PFAB' ix
fromAB' (Z a)     = fromA a
fromAB' (S (Z b)) = fromB b

toAB' :: PTwo ix -> PFAB' ix -> (Cons A (Cons B Nil)) ix
toAB' PZero         a = Z (toA a)
toAB' (PSucc PZero) b = S (Z (toB b))

