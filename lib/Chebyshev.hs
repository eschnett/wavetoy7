-- | Adapted from [math-functions-0.2.1.0] Numeric.Polynomial.Chebyshev
module Chebyshev ( chebyshev
                 , chebyshevApprox
                 , chebyshevApprox'
                 ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      )

import Data.Maybe

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
                   , RealFloat a, Fractional b
                   ) => Int -> (a -> b) -> v b
chebyshevApprox n = chebyshevApprox' (2 * n) n

chebyshevApprox' :: forall f a b.
                    ( Unfoldable f, Obj (Dom f) b
                    , RealFloat a, Fractional b
                    ) => Int -> Int -> (a -> b) -> f b
chebyshevApprox' np nc f =
    (fromJust . fromList) [coeff i | i <- [0..nc-1]]
    where coeff j = rf ((if j == 0 then 1 else 2) / fi np) *
                    sum [f (x k) * rf (c j k) | k <- [0..np-1]]
          t :: Int -> a
          t k = pi * (fi k + 0.5) / fi np
          x :: Int -> a
          x k = cos (t k)
          c :: Int -> Int -> a
          c j k = cos (fi j * t k)
          fi = fromIntegral
          rf = realToFrac
