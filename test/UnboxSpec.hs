{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module UnboxSpec where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Applicative(..), (<$>)
                      )
import qualified Prelude

import Data.Proxy
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving
import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Applicative
import Category
import Comonad
import Functor
import Unbox



newtype UA = UA Int
    deriving (Eq, Ord, Read, Show, Arbitrary, CoArbitrary)
instance Function UA where
    {-# INLINE function #-}
    function = functionMap (\(UA x) -> x) UA
derivingUnbox "UA"
    [t| UA -> Int |]
    [| \(UA x) -> x |]
    [| UA |]
newtype UB = UB Double
    deriving (Eq, Ord, Read, Show, Arbitrary, CoArbitrary)
instance Function UB where
    {-# INLINE function #-}
    function = functionMap (\(UB x) -> x) UB
derivingUnbox "UB"
    [t| UB -> Double |]
    [| \(UB x) -> x |]
    [| UB |]
newtype UC = UC Char
    deriving (Eq, Ord, Read, Show, Arbitrary, CoArbitrary)
instance Function UC where
    {-# INLINE function #-}
    function = functionMap (\(UC x) -> x) UC
derivingUnbox "UC"
    [t| UC -> Char |]
    [| \(UC x) -> x |]
    [| UC |]



prop_Unbox_Category_comp_id_left :: Fun UA UB -> UA -> Property
prop_Unbox_Category_comp_id_left (Fn f) x =
    uncurry (===) (getFnEqual (law_Category_comp_id_left f) x)

prop_Unbox_Category_comp_id_right :: Fun UA UB -> UA -> Property
prop_Unbox_Category_comp_id_right (Fn f) x =
    uncurry (===) (getFnEqual (law_Category_comp_id_right f) x)

prop_Unbox_Category_comp_assoc ::
    Fun UA UC -> Fun UB UA -> Fun UA UB -> UA -> Property
prop_Unbox_Category_comp_assoc (Fn h) (Fn g) (Fn f) x =
    uncurry (===) (getFnEqual (law_Category_comp_assoc h g f) x)



newtype Small1 a = Small1 a
    deriving (Eq, Ord, Read, Show, Prelude.Functor)
instance Arbitrary a => Arbitrary (Small1 a) where
    arbitrary = Small1 Prelude.<$> scale (`div` 10) arbitrary
    shrink (Small1 x) = Small1 Prelude.<$> shrink x



prop_VVector_Functor_id :: V.Vector A -> Property
prop_VVector_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_VVector_Functor_assoc :: Fun B C -> Fun A B -> V.Vector A -> Property
prop_VVector_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_UVector_Functor_id :: U.Vector UA -> Property
prop_UVector_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_UVector_Functor_assoc ::
    Fun UB UC -> Fun UA UB -> Small1 (U.Vector UA) -> Property
prop_UVector_Functor_assoc (Fn g) (Fn f) (Small1 xs) =
    uncurry (===) (getFnEqual (law_Functor_assoc (UFun g) (UFun f)) xs)



type N = 10
type N' = 5                     -- small



prop_CNVVector_Functor_id :: CNVVector N A -> Property
prop_CNVVector_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_CNVVector_Functor_assoc :: Fun B C -> Fun A B -> CNVVector N A -> Property
prop_CNVVector_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)



prop_CNUVector_Functor_id :: CNUVector N UA -> Property
prop_CNUVector_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_CNUVector_Functor_assoc ::
    Fun UB UC -> Fun UA UB -> CNUVector N UA -> Property
prop_CNUVector_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc (UFun g) (UFun f)) xs)



prop_CNVVector_Applicative_id :: CNVVector N A -> Property
prop_CNVVector_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_CNVVector_Applicative_comp ::
    Small1 (CNVVector N (Fun B C)) -> Small1 (CNVVector N (Fun A B)) ->
    Small1 (CNVVector N A) -> Property
prop_CNVVector_Applicative_comp (Small1 gs') (Small1 fs') (Small1 xs) =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_CNVVector_Applicative_homo :: Fun A B -> A -> Property
prop_CNVVector_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @(CNVVector N)) f x))

prop_CNVVector_Applicative_inter :: CNVVector N (Fun A B) -> A -> Property
prop_CNVVector_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))

prop_CNVVector_Applicative_id' :: Fun A B -> CNVVector N A -> Property
prop_CNVVector_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' f xs))

prop_CNVVector_Applicative_id_left' ::
    Fun (A, B) C -> A -> CNVVector N B -> Property
prop_CNVVector_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' f x ys))

prop_CNVVector_Applicative_id_right' ::
    Fun (A, B) C -> CNVVector N A -> B -> Property
prop_CNVVector_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' f xs y))

prop_CNVVector_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Small1 (CNVVector N A) -> Small1 (CNVVector N B) ->
    Small1 (CNVVector N C) -> Property
prop_CNVVector_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc' f g h i xs ys zs))



prop_CNUVector_Applicative_id' :: Fun UA UB -> CNUVector N UA -> Property
prop_CNUVector_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' (UFun f) xs))

prop_CNUVector_Applicative_id_left' ::
    Fun (UA *#* UB) UC -> UA -> CNUVector N UB -> Property
prop_CNUVector_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' (UFun f) x ys))

prop_CNUVector_Applicative_id_right' ::
    Fun (UA *#* UB) UC -> CNUVector N UA -> UB -> Property
prop_CNUVector_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' (UFun f) xs y))

prop_CNUVector_Applicative_assoc' ::
    Fun UA UA -> Fun UB UB -> Fun UC UC -> Fun (UA *#* (UB *#* UC)) UA ->
    CNUVector N' UA -> CNUVector N' UB -> CNUVector N' UC -> Property
prop_CNUVector_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) xs ys zs =
    uncurry (===) (getEqual (law_Applicative_assoc'
                                    (UFun f) (UFun g) (UFun h) (UFun i)
                                    xs ys zs))



prop_CNVVector_Comonad_extract :: Fun A B -> CNVVector N A -> Property
prop_CNVVector_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract f) xs)

prop_CNVVector_Comonad_duplicate :: CNVVector N A -> Property
prop_CNVVector_Comonad_duplicate xs =
    uncurry (===) (getFnEqual law_Comonad_duplicate xs)

prop_CNVVector_Comonad_extend ::
    Fun (CNVVector N A) B -> CNVVector N A -> Property
prop_CNVVector_Comonad_extend (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extend f) xs)

prop_CNVVector_Comonad_id_right :: CNVVector N A -> Property
prop_CNVVector_Comonad_id_right xs =
    uncurry (===) (getFnEqual law_Comonad_id_right xs)

prop_CNVVector_Comonad_id_left ::
    Fun (CNVVector N A) B -> CNVVector N A -> Property
prop_CNVVector_Comonad_id_left (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_id_left f) xs)

prop_CNVVector_Comonad_assoc ::
    Fun (CNVVector N A) B ->
    Fun (CNVVector N B) C ->
    Small1 (CNVVector N A) ->
    Property
prop_CNVVector_Comonad_assoc (Fn f) (Fn g) (Small1 xs) =
    uncurry (===) (getFnEqual (law_Comonad_assoc f g) xs)



prop_CNUVector_Comonad_extract :: Fun UA UB -> CNUVector N UA -> Property
prop_CNUVector_Comonad_extract (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_extract (UFun f)) xs)

-- prop_CNUVector_Comonad_duplicate :: CNUVector N UA -> Property
-- prop_CNUVector_Comonad_duplicate xs =
--     uncurry (===) (getFnEqual law_Comonad_duplicate xs)
-- 
-- prop_CNUVector_Comonad_extend ::
--     Fun (CNUVector N UA) UB -> CNUVector N UA -> Property
-- prop_CNUVector_Comonad_extend (Fn f) xs =
--     uncurry (===) (getFnEqual (law_Comonad_extend (UFun f)) xs)

prop_CNUVector_Comonad_id_right :: CNUVector N UA -> Property
prop_CNUVector_Comonad_id_right xs =
    uncurry (===) (getFnEqual law_Comonad_id_right xs)

prop_CNUVector_Comonad_id_left ::
    Fun (CNUVector N UA) UB -> CNUVector N UA -> Property
prop_CNUVector_Comonad_id_left (Fn f) xs =
    uncurry (===) (getFnEqual (law_Comonad_id_left f) xs)

prop_CNUVector_Comonad_assoc ::
    Fun (CNUVector N' UA) UB ->
    Fun (CNUVector N' UB) UC ->
    CNUVector N' UA ->
    Property
prop_CNUVector_Comonad_assoc (Fn f) (Fn g) xs =
    uncurry (===) (getFnEqual (law_Comonad_assoc f g) xs)
