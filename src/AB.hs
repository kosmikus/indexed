{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module AB where

import Combinators
import Typelevel
import EP

data A = AZero | ASucc B deriving (Show)
data B = BZero | BSucc A deriving (Show)

-- PFA :: Fin 0 + Fin 2 >>> o
type PFA = K () :+: (I (TRight (Succ Zero)))
type PFB = K () :+: (I (TRight (     Zero)))

-- PFAB :: Fin 0 >>> Fin 2
type PFAB = Fix (Tag Zero PFA :+: Tag (Succ Zero) PFB)

type PFAB' = PFAB PZero PTwo Nil

fromA :: A -> PFAB' Zero
fromA AZero     = Fix (LL (Tag PZero (LL (K ()))))
fromA (ASucc b) = Fix (LL (Tag PZero (RR (I (PRight (PSucc PZero)) (JR (fromB b))))))

toA :: PFAB' Zero -> A
toA (Fix (LL (Tag PZero (LL (K ())))))                            = AZero
toA (Fix (LL (Tag PZero (RR (I (PRight (PSucc PZero)) (JR b)))))) = ASucc (toB b)

fromB :: B -> PFAB' (Succ Zero)
fromB BZero     = Fix (RR (Tag (PSucc PZero) (LL (K ()))))
fromB (BSucc a) = Fix (RR (Tag (PSucc PZero) (RR (I (PRight PZero) (JR (fromA a))))))

toB :: PFAB' (Succ Zero) -> B
toB (Fix (RR (Tag (PSucc PZero) (LL (K ()))))) = BZero
toB (Fix (RR (Tag (PSucc PZero) (RR (I (PRight PZero) (JR a)))))) = BSucc (toA a)

fromAB' :: PTwo ix -> (Cons A (Cons B Nil)) ix -> PFAB' ix
fromAB' PZero         (Z a)     = fromA a
fromAB' (PSucc PZero) (S (Z b)) = fromB b

toAB' :: PTwo ix -> PFAB' ix -> (Cons A (Cons B Nil)) ix
toAB' PZero         a = Z (toA a)
toAB' (PSucc PZero) b = S (Z (toB b))

