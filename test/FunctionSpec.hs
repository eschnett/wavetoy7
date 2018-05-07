{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctionSpec where

import Test.QuickCheck
import Test.QuickCheck.Poly

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



prop_List_MFunctor_id :: [A] -> Property
prop_List_MFunctor_id xs =
    uncurry (===) (getFnEqual law_MFunctor_id xs)

prop_List_MFunctor_assoc :: Fun B C -> Fun A B -> [A] -> Property
prop_List_MFunctor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_MFunctor_assoc g f) xs)



prop_Function_MFunctor_id :: Fun B A -> NonEmptyList B -> Property
prop_Function_MFunctor_id (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual law_MFunctor_id xs
    in conjoin [u b === v b | b <- bs]

prop_Function_MFunctor_assoc ::
    Fun B C -> Fun A B -> Fun B A -> NonEmptyList B -> Property
prop_Function_MFunctor_assoc (Fn g) (Fn f) (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual (law_MFunctor_assoc g f) xs
    in conjoin [u b === v b | b <- bs]



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



prop_NList_MFunctor_id :: NList NA -> Property
prop_NList_MFunctor_id xs =
    uncurry (===) (getFnEqual law_MFunctor_id xs)

prop_NList_MFunctor_assoc :: Fun NB NC -> Fun NA NB -> NList NA -> Property
prop_NList_MFunctor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_MFunctor_assoc (NFun g) (NFun f)) xs)



prop_NFun_MFunctor_id :: Fun NB NA -> NonEmptyList NB -> Property
prop_NFun_MFunctor_id (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual law_MFunctor_id (NFun xs)
    in conjoin [chase u b === chase v b | b <- bs]

prop_NFun_MFunctor_assoc ::
    Fun NB NC -> Fun NA NB -> Fun NB NA -> NonEmptyList NB -> Property
prop_NFun_MFunctor_assoc (Fn g) (Fn f) (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual (law_MFunctor_assoc (NFun g) (NFun f)) (NFun xs)
    in conjoin [chase u b === chase v b | b <- bs]
