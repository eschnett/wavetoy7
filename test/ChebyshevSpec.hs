module ChebyshevSpec where

import Test.QuickCheck
import Test.QuickCheck.Instances()

import Chebyshev



-- | Approximate floating-point equality
approx :: (RealFrac a, Show a) => a -> a -> a -> Property
approx eps x y = counterexample (show x ++ " /= " ++ show y) (abs (x - y) < eps)

-- | n-th Chebyshev polynomial
cheb :: Num a => Int -> a -> a
cheb n = chebyshev (replicate n 0 ++ [1])

-- | Recurrence relation for Chebyshev polynomials
recur :: Num a => Int -> a -> a
recur n x = if | n == 0 -> 1
               | n == 1 -> x
               | otherwise -> 2 * x * cheb (n - 1) x - cheb (n - 2) x



prop_Chebyshev_recurrence ::
    NonNegative (Small Int) -> Integer -> Property
prop_Chebyshev_recurrence (NonNegative (Small n)) x =
    cheb n x === recur n x



-- prop_Chebyshev_approx :: NonNegative (Small Int) -> Property
-- prop_Chebyshev_approx (NonNegative (Small n)) =
--     conjoin (zipWith (approx 1.0e-13) coeffs' coeffs)
--     where phi :: Double -> Double
--           phi = cheb n
--           coeffs = replicate n 0 ++ [1] ++ replicate n 0
--           coeffs' = chebyshevApprox (2 * n + 1) phi



prop_Chebyshev_approx :: [Double] -> Property
prop_Chebyshev_approx cs' =
    conjoin (zipWith (approx (1.0e-13 * maxc)) cs fcs)
    where cs = cs' ++ [1]
          maxc = maximum (fmap abs cs)
          n = length cs
          f = chebyshev cs
          fcs = chebyshevApprox (2 * n) f
