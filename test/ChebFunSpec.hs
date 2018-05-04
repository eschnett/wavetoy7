{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ChebFunSpec where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      , concat, concatMap, sum, product, maximum, minimum
                      , and, or, all, any
                      , Applicative(..), (<$>)
                      )

import Data.Fixed
import Test.QuickCheck hiding (scale)

import Applicative
import Category
import ChebFun
import Foldable
import qualified Function as F
import Functor
import Unbox



maxabs :: (Foldable f, k ~ Dom f, Obj k a, Num a, Ord a) => f a -> a
maxabs = foldl (\r -> max r . abs) 0

sumabs :: (Foldable f, k ~ Dom f, Obj k a, Num a) => f a -> a
sumabs = foldl (\r -> (r +) . abs) 0

-- | Approximate floating-point equality
approx :: (RealFrac a, Show a) => a -> a -> a -> Property
approx delta x y = counterexample
                 (show x ++ " /= " ++ show y ++ "; " ++
                  "absdiff = " ++ show (y - x) ++ ", " ++
                  "reldiff = " ++ show ((y - x) / maxabs [x, y]) ++ "; " ++
                  "delta = " ++ show delta)
                 (abs (x - y) <= delta)

limitArg :: Real a => a -> a
limitArg x = mod' (x + 1) 2 - 1
limitFun :: ( Functor v, Cod v ~ (->), Foldable v
            , Obj (Dom v) b, Fractional b, Ord b)
            => ChebFun v a b -> ChebFun v a b
limitFun f = let scale = max 1 (sumabs (getChebFun f))
             in ChebFun (fmap (unapply (/ scale)) (getChebFun f))



type N = 10
type V = NUVector N

type CA = Double
type CB = Double
type CC = Double

eps :: Double
eps = 1.0e-12



prop_ChebFun_compact_inv :: CA -> Property
prop_ChebFun_compact_inv x' =
    uncurry (approx eps) (getFnEqual law_ChebFun_compact_inv x)
    where x = compactify x'

prop_ChebFun_compact_inv' :: CA -> Property
prop_ChebFun_compact_inv' x' =
    uncurry (approx eps) (getFnEqual law_ChebFun_compact_inv x)
    where x = mod' x' 2 - 1



prop_ChebFun_Functor_id :: ChebFun V CB CA -> Property
prop_ChebFun_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_ChebFun_Functor_assoc ::
    Fun CB CC -> Fun CA CB -> ChebFun V CB CA -> Property
prop_ChebFun_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc (UFun g) (UFun f)) xs)



prop_ChebFun_Applicative_id' :: Fun CA CB -> ChebFun V CB CA -> Property
prop_ChebFun_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' (UFun f) xs))

prop_ChebFun_Applicative_id_left' ::
    Fun (CA *#* CB) CC -> CA -> ChebFun V CB CB -> Property
prop_ChebFun_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' (UFun f) x ys))

prop_ChebFun_Applicative_id_right' ::
    Fun (CA *#* CB) CC -> ChebFun V CB CA -> CB -> Property
prop_ChebFun_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' (UFun f) xs y))

prop_ChebFun_Applicative_assoc' ::
    Fun CA CA -> Fun CB CB -> Fun CC CC -> Fun (CA *#* (CB *#* CC)) CA ->
    ChebFun V CB CA -> ChebFun V CB CB -> ChebFun V CB CC -> Property
prop_ChebFun_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) xs ys zs =
    uncurry (===) (getEqual (law_Applicative_assoc'
                                    (UFun f) (UFun g) (UFun h) (UFun i)
                                    xs ys zs))



prop_ChebVal_MCategory_comp_id_left :: ChebFun V CA CB -> CA -> Property
prop_ChebVal_MCategory_comp_id_left f' x' =
    uncurry (===) (F.getFnEqual (F.law_MCategory_comp_id_left f) x)
    where x = limitArg x'
          f = limitFun f'

prop_ChebVal_MCategory_comp_id_right :: ChebFun V CA CB -> CA -> Property
prop_ChebVal_MCategory_comp_id_right f' x' =
    uncurry (===) (F.getFnEqual (F.law_MCategory_comp_id_right f) x)
    where x = limitArg x'
          f = limitFun f'

prop_ChebVal_MCategory_comp_assoc ::
    ChebFun V CA CC -> ChebFun V CB CA -> ChebFun V CA CB -> CA -> Property
prop_ChebVal_MCategory_comp_assoc h' g' f' x' =
    uncurry (===) (F.getFnEqual (F.law_MCategory_comp_assoc h g f) x)
    where x = limitArg x'
          f = limitFun f'
          g = limitFun g'
          h = limitFun h'
