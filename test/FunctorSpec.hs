{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctorSpec where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )

import Control.Applicative (ZipList(..))
import Data.Constraint
import Data.Functor.Classes
import Data.Functor.Compose as F
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.List.NonEmpty
import Data.Proxy
import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category
import Functor



prop_Proxy_Functor_id :: Proxy A -> Property
prop_Proxy_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Proxy_Functor_assoc :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Proxy_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Identity_Functor_id :: Identity A -> Property
prop_Identity_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Identity_Functor_assoc :: Fun B C -> Fun A B -> Identity A -> Property
prop_Identity_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Either_Functor_id :: Either B A -> Property
prop_Either_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Either_Functor_assoc :: Fun B C -> Fun A B -> Either B A -> Property
prop_Either_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Tuple_Functor_id :: (B, A) -> Property
prop_Tuple_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Tuple_Functor_assoc :: Fun B C -> Fun A B -> (B, A) -> Property
prop_Tuple_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Function_Functor_id :: Fun B A -> NonEmptyList B -> Property
prop_Function_Functor_id (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual law_Functor_id xs
    in conjoin [u b === v b | b <- bs]

prop_Function_Functor_assoc ::
    Fun B C -> Fun A B -> Fun B A -> NonEmptyList B -> Property
prop_Function_Functor_assoc (Fn g) (Fn f) (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual (law_Functor_assoc g f) xs
    in conjoin [u b === v b | b <- bs]



newtype FA a = FA (Either A a)
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1)
instance Functor FA where
    type Dom FA = Dom (Either A)
    type Cod FA = Cod (Either A)
    proveCod = Sub Dict
    fmap f (FA xs) = FA (fmap f xs)

newtype FB a = FB (B, a)
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1)
instance Functor FB where
    type Dom FB = Dom ((,) B)
    type Cod FB = Cod ((,) B)
    proveCod = Sub Dict
    fmap f (FB xs) = FB (fmap f xs)

newtype FC a = FC [a]
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1)
instance Functor FC where
    type Dom FC = Dom []
    type Cod FC = Cod []
    proveCod = Sub Dict
    fmap f (FC xs) = FC (fmap f xs)



prop_Sum_Functor_id :: Sum FB FA A -> Property
prop_Sum_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Sum_Functor_assoc :: Fun B C -> Fun A B -> Sum FB FA A -> Property
prop_Sum_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Product_Functor_id :: Product FB FA A -> Property
prop_Product_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Product_Functor_assoc :: Fun B C -> Fun A B -> Product FB FA A -> Property
prop_Product_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Compose_Functor_id :: Compose FB FA A -> Property
prop_Compose_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Compose_Functor_assoc :: Fun B C -> Fun A B -> Compose FB FA A -> Property
prop_Compose_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Const_Functor_id :: Const B A -> Property
prop_Const_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Const_Functor_assoc :: Fun B C -> Fun A B -> Const B A -> Property
prop_Const_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_Maybe_Functor_id :: Maybe A -> Property
prop_Maybe_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Maybe_Functor_assoc :: Fun B C -> Fun A B -> Maybe A -> Property
prop_Maybe_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_List_Functor_id :: [A] -> Property
prop_List_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_List_Functor_assoc :: Fun B C -> Fun A B -> [A] -> Property
prop_List_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_NonEmpty_Functor_id :: NonEmpty A -> Property
prop_NonEmpty_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_NonEmpty_Functor_assoc :: Fun B C -> Fun A B -> NonEmpty A -> Property
prop_NonEmpty_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_ZipList_Functor_id :: ZipList A -> Property
prop_ZipList_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_ZipList_Functor_assoc :: Fun B C -> Fun A B -> ZipList A -> Property
prop_ZipList_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)
