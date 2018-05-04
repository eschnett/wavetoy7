{-# LANGUAGE UndecidableInstances #-}

module Domains where

import Data.Validity
import Numeric.IEEE
import GHC.Generics



-- x: (-\infty; +\infty)
-- sqrt: [0; +\infty)
-- sin: [-1; +1]
-- log: (0; +\infty)
-- atan: (-\pi/2; +\pi/2)
-- acos: [0; \pi)

data Constant
    = NegInf
    | Neg2Pi
    | NegPi
    | NegOne
    | NegPi2
    | Zero
    | PosInf
    | Pos2Pi
    | PosPi
    | PosOne
    | PosPi2

class Value (v :: Constant) where value :: IEEE a => a
instance Value 'NegInf where value = -infinity
instance Value 'Neg2Pi where value = -2*pi
instance Value 'NegPi  where value = -pi
instance Value 'NegOne where value = -1
instance Value 'NegPi2 where value = -pi/2
instance Value 'Zero   where value = 0
instance Value 'PosPi2 where value = pi/2
instance Value 'PosOne where value = 1
instance Value 'PosPi  where value = pi
instance Value 'Pos2Pi where value = 2*pi
instance Value 'PosInf where value = infinity



newtype BoundedReal (min :: Constant) (max :: Constant) a = B { getB :: a }
    deriving ( Eq, Ord, Read, Show, Generic
             , Floating, Fractional, IEEE, Num, Real, RealFloat, RealFrac)

instance (Value min, Value max, IEEE a) => Bounded (BoundedReal min max a) where
    minBound = B (value @min)
    maxBound = B (value @max)

instance (Bounded (BoundedReal min max a), IEEE a, Validity a)
        => Validity (BoundedReal min max a) where
    isValid x = (isNaN x || x >= minBound && x <= maxBound) && isValid (getB x)
