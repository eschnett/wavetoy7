{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CategorySpec where

import Prelude hiding (id, (.), curry, uncurry)

import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category



prop_Hask_Category_comp_id_left :: Fun A B -> A -> Property
prop_Hask_Category_comp_id_left (Fn f) x =
    uncurry (===) (getFnEqual (law_Category_comp_id_left f) x)

prop_Hask_Category_comp_id_right :: Fun A B -> A -> Property
prop_Hask_Category_comp_id_right (Fn f) x =
    uncurry (===) (getFnEqual (law_Category_comp_id_right f) x)

prop_Hask_Category_comp_assoc :: Fun A C -> Fun B A -> Fun A B -> A -> Property
prop_Hask_Category_comp_assoc (Fn h) (Fn g) (Fn f) x =
    uncurry (===) (getFnEqual (law_Category_comp_assoc h g f) x)
