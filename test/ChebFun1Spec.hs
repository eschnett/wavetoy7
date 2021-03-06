{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ChebFun1Spec where

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
import ChebFun1
import Foldable
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
limitFun :: (Unbox b, Fractional b, Ord b) => ChebFun n a b -> ChebFun n a b
limitFun f = let ChebFun cs = f
                 scale = max 1 (sumabs cs)
             in ChebFun (fmap (unapply (/ scale)) cs)



type N = 10
type N' = 2

type CA = Double
type CB = Double
type CC = Double

eps :: Double
eps = 1.0e-12



prop_ChebFun1_compact_inv :: CA -> Property
prop_ChebFun1_compact_inv x' =
    uncurry (approx eps) (getFnEqual law_ChebFun_compact_inv x)
    where x = compactify x'

prop_ChebFun1_compact_inv' :: CA -> Property
prop_ChebFun1_compact_inv' x' =
    uncurry (approx eps) (getFnEqual law_ChebFun_compact_inv x)
    where x = mod' x' 2 - 1



prop_ChebFun1_Category_comp_id_left :: ChebFun N CA CB -> CA -> Property
prop_ChebFun1_Category_comp_id_left f' x' =
    uncurry (approx eps) (getFnEqual (law_Category_comp_id_left f) x)
    where x = limitArg x'
          f = limitFun f'

prop_ChebFun1_Category_comp_id_right :: ChebFun N CA CB -> CA -> Property
prop_ChebFun1_Category_comp_id_right f' x' =
    uncurry (approx eps) (getFnEqual (law_Category_comp_id_right f) x)
    where x = limitArg x'
          f = limitFun f'
    -- where x = mod' x' 2 - 1
    --       eps = let (ChebFun cs) = f in eps1 * max 1 (maxabs cs)

-- TODO: Make this work for larger N'
prop_ChebFun1_Category_comp_assoc ::
    ChebFun N' CA CC -> ChebFun N' CB CA -> ChebFun N' CA CB -> CA -> Property
prop_ChebFun1_Category_comp_assoc h' g' f' x' =
    uncurry (approx eps) (getFnEqual (law_Category_comp_assoc h g f) x)
    where x = limitArg x'
          f = limitFun f'
          g = limitFun g'
          h = limitFun h'



prop_ChebFun1_Functor_id :: ChebFun N CB CA -> Property
prop_ChebFun1_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_ChebFun1_Functor_assoc ::
    Fun CB CC -> Fun CA CB -> ChebFun N CB CA -> Property
prop_ChebFun1_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc (UFun g) (UFun f)) xs)



prop_ChebFun1_Applicative_id' :: Fun CA CB -> ChebFun N CB CA -> Property
prop_ChebFun1_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' (UFun f) xs))

prop_ChebFun1_Applicative_id_left' ::
    Fun (CA *#* CB) CC -> CA -> ChebFun N CB CB -> Property
prop_ChebFun1_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' (UFun f) x ys))

prop_ChebFun1_Applicative_id_right' ::
    Fun (CA *#* CB) CC -> ChebFun N CB CA -> CB -> Property
prop_ChebFun1_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' (UFun f) xs y))

prop_ChebFun1_Applicative_assoc' ::
    Fun CA CA -> Fun CB CB -> Fun CC CC -> Fun (CA *#* (CB *#* CC)) CA ->
    ChebFun N CB CA -> ChebFun N CB CB -> ChebFun N CB CC -> Property
prop_ChebFun1_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) xs ys zs =
    uncurry (===) (getEqual (law_Applicative_assoc'
                                    (UFun f) (UFun g) (UFun h) (UFun i)
                                    xs ys zs))
