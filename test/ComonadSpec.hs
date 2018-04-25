{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ComonadSpec where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )
import qualified Prelude
import Data.Constraint
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.List.NonEmpty
import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category
import Comonad
import Functor



instance Function a => Function (Identity a) where
    function = functionMap runIdentity Identity

instance (CoArbitrary (f a), CoArbitrary (g a)) => CoArbitrary (F.Sum f g a)

instance (CoArbitrary (f a), CoArbitrary (g a)) => CoArbitrary (F.Product f g a)

instance (Function (f a), Function (g a)) => Function (F.Sum f g a) where
    function = functionMap p q
        where p (InL xs) = Left xs
              p (InR xs) = Right xs
              q (Left xs) = InL xs
              q (Right xs) = InR xs

instance (Function (f a), Function (g a)) => Function (F.Product f g a) where
    function = functionMap p q
        where p (Pair xs ys) = (xs, ys)
              q (xs, ys) = Pair xs ys



prop_Identity_Comonad_extract :: Fun A B -> Identity A -> Property
prop_Identity_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract f) xs)

prop_Identity_Comonad_duplicate :: Identity A -> Property
prop_Identity_Comonad_duplicate xs =
    uncurry (===) (getFnEqual law_Comonad_duplicate xs)

prop_Identity_Comonad_extend :: Fun (Identity A) B -> Identity A -> Property
prop_Identity_Comonad_extend (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extend f) xs)



prop_Tuple_Comonad_extract :: Fun A B -> (B, A) -> Property
prop_Tuple_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract f) xs)

prop_Tuple_Comonad_duplicate :: (B, A) -> Property
prop_Tuple_Comonad_duplicate xs =
    uncurry (===) (getFnEqual law_Comonad_duplicate xs)

prop_Tuple_Comonad_extend :: Fun (B, A) B -> (B, A) -> Property
prop_Tuple_Comonad_extend (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extend f) xs)



newtype FA a = FA (NonEmpty a)
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1, CoArbitrary)
instance Function a => Function (FA a) where
    function = functionMap (\(FA x) -> x) FA
instance Functor FA where
    type Dom FA = Dom Identity
    type Cod FA = Cod Identity
    proveCod = Sub Dict
    fmap f (FA xs) = FA (fmap f xs)
instance Comonad FA where
    extract (FA xs) = extract xs
    extend f (FA xs) = FA (extend (f . FA) xs)

newtype FB a = FB (B, a)
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1, CoArbitrary)
instance Function a => Function (FB a) where
    function = functionMap (\(FB x) -> x) FB
instance Functor FB where
    type Dom FB = Dom ((,) B)
    type Cod FB = Cod ((,) B)
    proveCod = Sub Dict
    fmap f (FB xs) = FB (fmap f xs)
instance Comonad FB where
    extract (FB xs) = extract xs
    extend f (FB xs) = FB (extend (f . FB) xs)

newtype FC a = FC [a]
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1, CoArbitrary)
instance Function a => Function (FC a) where
    function = functionMap (\(FC x) -> x) FC
instance Functor FC where
    type Dom FC = Dom []
    type Cod FC = Cod []
    proveCod = Sub Dict
    fmap f (FC xs) = FC (fmap f xs)



prop_Sum_Comonad_extract :: Fun A B -> Sum FB FA A -> Property
prop_Sum_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract f) xs)

prop_Sum_Comonad_duplicate :: Sum FB FA A -> Property
prop_Sum_Comonad_duplicate xs =
    uncurry (===) (getFnEqual law_Comonad_duplicate xs)

prop_Sum_Comonad_extend :: Fun (Sum FB FA A) B -> Sum FB FA A -> Property
prop_Sum_Comonad_extend (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extend f) xs)



prop_Product_Comonad_extract :: Fun A B -> Product FB FA A -> Property
prop_Product_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract f) xs)

prop_Product_Comonad_duplicate :: Product FB FA A -> Property
prop_Product_Comonad_duplicate xs =
    uncurry (===) (getFnEqual law_Comonad_duplicate xs)

prop_Product_Comonad_extend ::
    Fun (Product FB FA A) B -> Product FB FA A -> Property
prop_Product_Comonad_extend (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extend f) xs)



newtype Small1 a = Small1 a
    deriving (Eq, Ord, Read, Show, Prelude.Functor)
instance Arbitrary a => Arbitrary (Small1 a) where
    arbitrary = Small1 Prelude.<$> scale (`div` 10) arbitrary
    shrink (Small1 x) = Small1 Prelude.<$> shrink x



prop_NonEmpty_Comonad_extract :: Fun A B -> NonEmpty A -> Property
prop_NonEmpty_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract f) xs)

prop_NonEmpty_Comonad_duplicate :: NonEmpty A -> Property
prop_NonEmpty_Comonad_duplicate xs =
    uncurry (===) (getFnEqual law_Comonad_duplicate xs)

prop_NonEmpty_Comonad_extend ::
    Fun (NonEmpty A) B -> Small1 (NonEmpty A) -> Property
prop_NonEmpty_Comonad_extend (Fn f) (Small1 xs) =
    uncurry (===) (getFnEqual (law_Comonad_extend f) xs)
