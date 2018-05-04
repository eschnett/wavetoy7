{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctionSpec where

import Data.Fixed
import Test.QuickCheck
import Test.QuickCheck.Poly

import ChebFun
import Function



prop_Hask_MCategory_comp_id_left :: Fun A B -> A -> Property
prop_Hask_MCategory_comp_id_left (Fn f) x =
    uncurry (===) (getFnEqual (law_MCategory_comp_id_left f) x)

prop_Hask_MCategory_comp_id_right :: Fun A B -> A -> Property
prop_Hask_MCategory_comp_id_right (Fn f) x =
    uncurry (===) (getFnEqual (law_MCategory_comp_id_right f) x)

prop_Hask_MCategory_comp_assoc :: Fun A C -> Fun B A -> Fun A B -> A -> Property
prop_Hask_MCategory_comp_assoc (Fn h) (Fn g) (Fn f) x =
    uncurry (===) (getFnEqual (law_MCategory_comp_assoc h g f) x)



newtype NA = NA Integer
    deriving (Eq, Ord, Read, Show, Num, Arbitrary, CoArbitrary)
instance Function NA where
    function = functionMap (\(NA x) -> x) NA
newtype NB = NB Integer
    deriving (Eq, Ord, Read, Show, Num, Arbitrary, CoArbitrary)
instance Function NB where
    function = functionMap (\(NB x) -> x) NB
newtype NC = NC Integer
    deriving (Eq, Ord, Read, Show, Num, Arbitrary, CoArbitrary)
instance Function NC where
    function = functionMap (\(NC x) -> x) NC



prop_Num_MCategory_comp_id_left :: Fun NA NB -> NA -> Property
prop_Num_MCategory_comp_id_left (Fn f) x =
    uncurry (===) (getFnEqual (law_MCategory_comp_id_left (NFun f)) x)

prop_Num_MCategory_comp_id_right :: Fun NA NB -> NA -> Property
prop_Num_MCategory_comp_id_right (Fn f) x =
    uncurry (===) (getFnEqual (law_MCategory_comp_id_right (NFun f)) x)

prop_Num_MCategory_comp_assoc ::
    Fun NA NC -> Fun NB NA -> Fun NA NB -> NA -> Property
prop_Num_MCategory_comp_assoc (Fn h) (Fn g) (Fn f) x =
    uncurry (===) (getFnEqual (law_MCategory_comp_assoc
                                      (NFun h) (NFun g) (NFun f)) x)
