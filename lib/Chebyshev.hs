{-# LANGUAGE UndecidableInstances #-}

-- | Adapted from [math-functions-0.2.1.0] Numeric.Polynomial.Chebyshev
module Chebyshev ( chebyshev
                 -- , Floating'(..)
                 , chebyshevApprox
                 , chebyshevApprox'
                 ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      )

-- import Data.Fixed
import Data.Maybe
-- import Data.Ratio

import Category
import Foldable
import Functor
import Unfoldable



-- $chebyshev
--
-- A Chebyshev polynomial of the first kind is defined by the
-- following recurrence:
--
-- \[\begin{aligned}
--     T_0(x)     &= 1 \\
--     T_1(x)     &= x \\
--     T_{n+1}(x) &= 2xT_n(x) - T_{n-1}(x) \\
-- \end{aligned}
-- \]



data C a = C !a !a



-- | Evaluate a Chebyshev polynomial of the first kind, using the
-- Clenshaw algorithm; see
-- <https://en.wikipedia.org/wiki/Clenshaw_algorithm>.
chebyshev :: (Foldable v, Obj (Dom v) a, Num a)
             => v a   -- ^ Polynomial coefficients in increasing order
             -> a     -- ^ Position
             -> a
chebyshev cs' x =
    if null cs then 0 else fini . foldr step (C 0 0) . tail $ cs
    where cs = toList cs'
          step k (C b0 b1) = C (k + 2 * x * b0 - b1) b0
          fini   (C b0 b1) = head cs + x * b0 - b1
{-# INLINE chebyshev #-}



-- | Approximate a given function via Chebyshev polynomials.
-- See <http://mathworld.wolfram.com/ChebyshevApproximationFormula.html>.
chebyshevApprox :: ( Unfoldable v, Obj (Dom v) b
                   , RealFrac a, Floating' a, Fractional b
                   ) => Int -> (a -> b) -> v b
chebyshevApprox n = chebyshevApprox' (2 * n) n

chebyshevApprox' :: forall f a b.
                    ( Unfoldable f, Obj (Dom f) b
                    , RealFrac a, Floating' a, Fractional b
                    ) => Int -> Int -> (a -> b) -> f b
chebyshevApprox' np nc f =
    (fromJust . fromList) [coeff i | i <- [0..nc-1]]
    where coeff j = rf ((if j == 0 then 1 else 2) / fi np) *
                    sum [f (x k) * rf (c j k) | k <- [0..np-1]]
          t :: Int -> a
          t k = fi (2 * k + 1) / fi (2 * np)
          x :: Int -> a
          x k = cospi' (t k)
          c :: Int -> Int -> a
          -- c j k = cos (pi * fi j * t k)
          c j k = cospi' (u j k)
          u :: Int -> Int -> a
          u j k = fi jk / fi (2 * np)
              where jk = (j * (2 * k + 1)) `mod` (4 * np)
          fi = fromIntegral
          rf = realToFrac

class Floating' a where cospi' :: a -> a
instance Floating a => Floating' a where cospi' x = cos (pi * x)

-- class Floating' a where
--     cospi' :: a -> a
-- 
-- instance Floating a => Floating' a where
--     cospi' x = cos (pi * x)
-- 
-- instance Integral a => Floating' (Ratio a) where
--     cospi' x =
--         let x1 = x `mod'` 2
--             x2 = if x1 <= 1 then x1 else 2 - x1
--         in if x2 <= 1/2 then c x2 else - c (1 - x2)
--         where c y = (1 - 4 * y^2) / (1 + y^2)
