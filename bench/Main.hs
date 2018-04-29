import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      , concat, concatMap, sum, product, and, or, all, any
                      , Applicative(..), (<$>)
                      )
import qualified Prelude

import Criterion.Main
import Data.Constraint
import Data.Monoid
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U

import Applicative
import Category
import Foldable
import Functor
import Unbox



type N = 1000



vsum0 :: Num a => a -> V.Vector a -> a
vsum0 r xs = r + V.sum xs

bench_vsum0 :: Double -> Double
bench_vsum0 r = let xs :: V.Vector Double
                    xs = V.replicate (intVal @N) 1
                in xs `seq` vsum0 r xs

usum0 :: (Unbox a, Num a) => a -> U.Vector a -> a
usum0 r xs = r + U.sum xs

bench_usum0 :: Double -> Double
bench_usum0 r = let xs :: U.Vector Double
                    xs = U.replicate (intVal @N) 1
                in xs `seq` usum0 r xs

vsum :: (Functor f, Foldable f, Cod f ~ (->), Obj (Dom f) a, Num a)
        => a -> f a -> a
vsum r xs = r + sum xs

bench_vsum1 :: Double -> Double
bench_vsum1 r = let xs :: V.Vector Double
                    xs = V.replicate (intVal @N) 1
                in xs `seq` vsum r xs

bench_usum1 :: Double -> Double
bench_usum1 r = let xs :: U.Vector Double
                    xs = U.replicate (intVal @N) 1
                in xs `seq` vsum r xs

bench_vsum2 :: Double -> Double
bench_vsum2 r = let xs :: NVVector N Double
                    xs = WithSize (V.replicate (intVal @N) 1)
                in xs `seq` vsum r xs

bench_usum2 :: Double -> Double
bench_usum2 r = let xs :: NUVector N Double
                    xs = WithSize (U.replicate (intVal @N) 1)
                in xs `seq` vsum r xs

bench_vsum3 :: Double -> Double
bench_vsum3 r = let xs :: CNVVector N Double
                    xs = WithPointer 0 (WithSize (V.replicate (intVal @N) 1))
                in xs `seq` vsum r xs

bench_usum3 :: Double -> Double
bench_usum3 r = let xs :: CNUVector N Double
                    xs = WithPointer 0 (WithSize (U.replicate (intVal @N) 1))
                in xs `seq` vsum r xs



vdot0 :: Num a => a -> V.Vector a -> V.Vector a -> a
vdot0 r xs ys = r + V.sum (V.zipWith (+) xs ys)

bench_vdot0 :: Double -> Double
bench_vdot0 r = let xs :: V.Vector Double
                    xs = V.replicate (intVal @N) 1
                    ys :: V.Vector Double
                    ys = V.replicate (intVal @N) 2
                in xs `seq` ys `seq` vdot0 r xs ys

udot0 :: (Unbox a, Num a) => a -> U.Vector a -> U.Vector a -> a
udot0 r xs ys = r + U.sum (U.zipWith (+) xs ys)

bench_udot0 :: Double -> Double
bench_udot0 r = let xs :: U.Vector Double
                    xs = U.replicate (intVal @N) 1
                    ys :: U.Vector Double
                    ys = U.replicate (intVal @N) 2
                in xs `seq` ys `seq` udot0 r xs ys

vdot :: (Applicative f, Foldable f, Cod f ~ (->), Dom f ~ (->), Num a)
         => a -> f a -> f a -> a
vdot r xs ys = r + sum (liftA2 (+) xs ys)

vdot' :: forall f k p a.
         ( Applicative f, Foldable f, Cod f ~ (->)
         , k ~ Dom f, Cartesian k, p ~ Prod k
         , Obj k a, Num a)
         => a -> f a -> f a -> a
vdot' r xs ys = r + sum (liftA2' (unapply (uncurry (+) . unprod)) (xs, ys))
                \\ (proveCartesian @k :: (Obj k a, Obj k a) :- Obj k (p a a))
-- vdot' r xs ys = r + sum (liftA2' add (xs, ys))
--                    where {-# INLINE add #-}
--                          add :: p a a `k` a
--                          add = unapply (uncurry (+) . unprod)
--                                \\ (proveCartesian @k ::
--                                        (Obj k a, Obj k a) :- Obj k (p a a))
--                          -- add :: (a, a) -> a
--                          -- add (x, y) = x + y
--                          -- add :: (a *#* a) -#> a
--                          -- add = UFun $ \(UProd (x, y)) -> x + y
--                          --       \\ (proveCartesian @k ::
--                          --               (Obj k a, Obj k a) :- Obj k (p a a))

-- bench_vdot1 :: Double -> Double
-- bench_vdot1 r = let xs :: V.Vector Double
--                     xs = V.replicate (intVal @N) 1
--                     ys :: V.Vector Double
--                     ys = V.replicate (intVal @N) 2
--                 in xs `seq` ys `seq` vdot r xs ys
-- 
-- bench_vdot1' :: Double -> Double
-- bench_vdot1' r = let xs :: V.Vector Double
--                      xs = V.replicate (intVal @N) 1
--                      ys :: V.Vector Double
--                      ys = V.replicate (intVal @N) 2
--                  in xs `seq` ys `seq` vdot' r xs ys
-- 
-- bench_udot1' :: Double -> Double
-- bench_udot1' r = let xs :: U.Vector Double
--                      xs = U.replicate (intVal @N) 1
--                      ys :: U.Vector Double
--                      ys = U.replicate (intVal @N) 2
--                  in xs `seq` ys `seq` vdot' r xs ys

bench_vdot2 :: Double -> Double
bench_vdot2 r = let xs :: NVVector N Double
                    xs = WithSize (V.replicate (intVal @N) 1)
                    ys :: NVVector N Double
                    ys = WithSize (V.replicate (intVal @N) 2)
                in xs `seq` ys `seq` vdot r xs ys

bench_vdot2' :: Double -> Double
bench_vdot2' r = let xs :: NVVector N Double
                     xs = WithSize (V.replicate (intVal @N) 1)
                     ys :: NVVector N Double
                     ys = WithSize (V.replicate (intVal @N) 2)
                 in xs `seq` ys `seq` vdot' r xs ys

bench_udot2' :: Double -> Double
bench_udot2' r = let xs :: NUVector N Double
                     xs = WithSize (U.replicate (intVal @N) 1)
                     ys :: NUVector N Double
                     ys = WithSize (U.replicate (intVal @N) 2)
                 in xs `seq` ys `seq` vdot' r xs ys

bench_vdot3 :: Double -> Double
bench_vdot3 r = let xs :: CNVVector N Double
                    xs = WithPointer 0 (WithSize (V.replicate (intVal @N) 1))
                    ys :: CNVVector N Double
                    ys = WithPointer 0 (WithSize (V.replicate (intVal @N) 2))
                in xs `seq` ys `seq` vdot r xs ys

bench_vdot3' :: Double -> Double
bench_vdot3' r = let xs :: CNVVector N Double
                     xs = WithPointer 0 (WithSize (V.replicate (intVal @N) 1))
                     ys :: CNVVector N Double
                     ys = WithPointer 0 (WithSize (V.replicate (intVal @N) 2))
                 in xs `seq` ys `seq` vdot' r xs ys

bench_udot3' :: Double -> Double
bench_udot3' r = let xs :: CNUVector N Double
                     xs = WithPointer 0 (WithSize (U.replicate (intVal @N) 1))
                     ys :: CNUVector N Double
                     ys = WithPointer 0 (WithSize (U.replicate (intVal @N) 2))
                 in xs `seq` ys `seq` vdot' r xs ys



main :: IO ()
main = defaultMain [
        bgroup "vsum" [ bench "vsum0" (whnf bench_vsum0 0)
                      , bench "vsum1" (whnf bench_vsum1 0)
                      , bench "vsum2" (whnf bench_vsum2 0)
                      , bench "vsum3" (whnf bench_vsum3 0)
                      , bench "usum0" (whnf bench_usum0 0)
                      , bench "usum1" (whnf bench_usum1 0)
                      , bench "usum2" (whnf bench_usum2 0)
                      , bench "usum3" (whnf bench_usum3 0)
                      ],
        bgroup "vdot" [ bench "vdot0" (whnf bench_vdot0 0)
                      , bench "vdot2" (whnf bench_vdot2 0)
                      , bench "vdot2'" (whnf bench_vdot2' 0)
                      , bench "vdot3" (whnf bench_vdot3 0)
                      , bench "vdot3'" (whnf bench_vdot3' 0)
                      , bench "udot0" (whnf bench_udot0 0)
                      , bench "udot2'" (whnf bench_udot2' 0)
                      , bench "udot3'" (whnf bench_udot3' 0)
                      ]]
