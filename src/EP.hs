{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module EP where


import Universe
import Map

-------------------------------------------------------------------------------
-- Conversion to/from user datatypes
-------------------------------------------------------------------------------

newtype I0 r = I0 { unI0 :: r }

class Fam (phi :: * -> *) where
  type PF phi :: Code * *
  type Rec phi :: * -> *
  from :: phi ix -> ix -> Interprt (PF phi) (Rec phi) ix
  to   :: phi ix -> Interprt (PF phi) (Rec phi) ix -> ix

-- Unused so far
class El (phi :: i -> *) (ix :: i) where
  proof :: phi ix

-------------------------------------------------------------------------------
-- Example: mutual recursion, no parameters
-------------------------------------------------------------------------------

data Zig = Zig Zag | ZigEnd
data Zag = Zag Zig

data ZigZag ix where
  ZigZag_Zig :: ZigZag Zig
  ZigZag_Zag :: ZigZag Zag

instance Fam ZigZag where
  type PF ZigZag = FIX (SUM (PROD (O Zig) (SUM (I (R Zag)) UNIT))
                            (PROD (O Zag) (I (R Zig))))
  type Rec ZigZag = I0

  from ZigZag_Zig (Zig zag) = I_F (I_L (I_P I_O (I_L (I_I (RR (from ZigZag_Zag zag))))))
  from ZigZag_Zig (ZigEnd)  = I_F (I_L (I_P I_O (I_R I_U)))
  from ZigZag_Zag (Zag zig) = I_F (I_R (I_P I_O (I_I (RR (from ZigZag_Zig zig)))))

  to ZigZag_Zig (I_F (I_L (I_P I_O (I_L (I_I (RR zag)))))) = Zig (to ZigZag_Zag zag)
  to ZigZag_Zig (I_F (I_L (I_P I_O (I_R I_U))))            = ZigEnd
  to ZigZag_Zag (I_F (I_R (I_P I_O (I_I (RR zig)))))       = Zag (to ZigZag_Zig zig)

instance El ZigZag Zig where
  proof = ZigZag_Zig

instance El ZigZag Zag where
  proof = ZigZag_Zag

zigZag :: Zig
zigZag = Zig (Zag (Zig (Zag ZigEnd)))

-------------------------------------------------------------------------------
-- Example: mutual recursion, one parameter
-------------------------------------------------------------------------------

data ZigA a = ZigA (ZagA a) | ZigEndA a deriving Show
data ZagA a = ZagA (ZigA a)             deriving Show

data ZigZagA a ix where
  ZigZagA_ZigA :: ZigZagA a (ZigA a)
  ZigZagA_ZagA :: ZigZagA a (ZagA a)

data Const a (b :: *) = C { unC :: a }

instance Fam (ZigZagA a) where
  type PF (ZigZagA a) = FIX (SUM (PROD (O (ZigA a)) (SUM (I (R (ZagA a))) (I (L a))))
                                 (PROD (O (ZagA a)) (I (R (ZigA a)))))
  type Rec (ZigZagA a) = Const a

  from ZigZagA_ZigA (ZigA zag)  = I_F (I_L (I_P I_O (I_L (I_I (RR (from ZigZagA_ZagA zag))))))
  from ZigZagA_ZigA (ZigEndA a) = I_F (I_L (I_P I_O (I_R (I_I (LL (C a))))))
  from ZigZagA_ZagA (ZagA zig)  = I_F (I_R (I_P I_O (I_I (RR (from ZigZagA_ZigA zig)))))

  to ZigZagA_ZigA (I_F (I_L (I_P I_O (I_L (I_I (RR zag))))))    = ZigA (to ZigZagA_ZagA zag)
  to ZigZagA_ZigA (I_F (I_L (I_P I_O (I_R (I_I (LL (C a))))))) = ZigEndA a
  to ZigZagA_ZagA (I_F (I_R (I_P I_O (I_I (RR zig)))))          = ZagA (to ZigZagA_ZigA zig)

zigZagA :: ZigA Int
zigZagA = ZigA (ZagA (ZigA (ZagA (ZigEndA 0))))

testZigZagA :: ZigA Int
testZigZagA = to ZigZagA_ZigA . imap (up (+1)) . from ZigZagA_ZigA $ zigZagA

up :: (a -> b) -> (Const a :->: Const b)
up f (C x) = C (f x)
