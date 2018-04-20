{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ApplicativeSpec where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Applicative(..), (<$>)
                      )
import qualified Prelude

import Data.Constraint
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
-- import Data.Monoid hiding ((<>), Sum(..), Product(..))
import qualified Data.Monoid as Monoid
import Data.Proxy
import Data.Semigroup hiding (Sum(..), Product(..))
import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category
import Functor
import Applicative



prop_Proxy_Applicative_id :: Proxy A -> Property
prop_Proxy_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Proxy_Applicative_comp ::
    Proxy (Fun B C) -> Proxy (Fun A B) -> Proxy A -> Property
prop_Proxy_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Proxy_Applicative_homo :: Fun A B -> A -> Property
prop_Proxy_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @Proxy) f x))

prop_Proxy_Applicative_inter :: Proxy (Fun A B) -> A -> Property
prop_Proxy_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Identity_Applicative_id :: Identity A -> Property
prop_Identity_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Identity_Applicative_comp ::
    Identity (Fun B C) -> Identity (Fun A B) -> Identity A -> Property
prop_Identity_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Identity_Applicative_homo :: Fun A B -> A -> Property
prop_Identity_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @Identity) f x))

prop_Identity_Applicative_inter :: Identity (Fun A B) -> A -> Property
prop_Identity_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Either_Applicative_id :: Either B A -> Property
prop_Either_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Either_Applicative_comp ::
    Either B (Fun B C) -> Either B (Fun A B) -> Either B A -> Property
prop_Either_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Either_Applicative_homo :: Fun A B -> A -> Property
prop_Either_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @(Either B)) f x))

prop_Either_Applicative_inter :: Either B (Fun A B) -> A -> Property
prop_Either_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



newtype M = M (Monoid.Sum Integer)
    deriving (Eq, Show, Arbitrary)
instance Semigroup M where
    M x <> M y = M (x <> y)
instance Monoid M where
    mempty = M mempty
    mappend = (<>)

prop_Tuple_Applicative_id :: (M, A) -> Property
prop_Tuple_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Tuple_Applicative_comp ::
    (M, Fun B C) -> (M, Fun A B) -> (M, A) -> Property
prop_Tuple_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Tuple_Applicative_homo :: Fun A B -> A -> Property
prop_Tuple_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @((,) M)) f x))

prop_Tuple_Applicative_inter :: (M, Fun A B) -> A -> Property
prop_Tuple_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Function_Applicative_id :: Fun B A -> [B] -> Property
prop_Function_Applicative_id (Fn xs) bs =
    let (u, v) = getEqual (law_Applicative_id xs)
    in conjoin [u b === v b | b <- bs]

prop_Function_Applicative_comp ::
    Fun B (Fun B C) -> Fun B (Fun A B) -> Fun B A -> [B] -> Property
prop_Function_Applicative_comp (Fn gs') (Fn fs') (Fn xs) bs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
        (u, v) = getEqual (law_Applicative_comp gs fs xs)
    in conjoin [u b === v b | b <- bs]

prop_Function_Applicative_homo :: Fun A B -> A -> [B] -> Property
prop_Function_Applicative_homo (Fn f) x bs =
    let (u, v) = getEqual (law_Applicative_homo (Proxy @((->) B)) f x)
    in conjoin [u b === v b | b <- bs]

prop_Function_Applicative_inter :: Fun B (Fun A B) -> A -> [B] -> Property
prop_Function_Applicative_inter (Fn fs') x bs =
    let fs = applyFun <$> fs'
        (u, v) = getEqual (law_Applicative_inter fs x)
    in conjoin [u b === v b | b <- bs]



newtype FA a = FA (Either A a)
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1)
instance Functor FA where
    type Dom FA = Dom (Either A)
    type Cod FA = Cod (Either A)
    proveCod = Sub Dict
    fmap f (FA xs) = FA (fmap f xs)
instance Applicative FA where
    pure x = FA (pure x)
    liftA2 f (FA xs) (FA ys) = FA (liftA2 f xs ys)

newtype FB a = FB (M, a)
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1)
instance Functor FB where
    type Dom FB = Dom ((,) M)
    type Cod FB = Cod ((,) M)
    proveCod = Sub Dict
    fmap f (FB xs) = FB (fmap f xs)
instance Applicative FB where
    pure x = FB (pure x)
    liftA2 f (FB xs) (FB ys) = FB (liftA2 f xs ys)

newtype FC a = FC [a]
    deriving (Eq, Eq1, Show, Show1, Arbitrary, Arbitrary1)
instance Functor FC where
    type Dom FC = Dom []
    type Cod FC = Cod []
    proveCod = Sub Dict
    fmap f (FC xs) = FC (fmap f xs)
instance Applicative FC where
    pure x = FC (pure x)
    liftA2 f (FC xs) (FC ys) = FC (liftA2 f xs ys)



prop_Product_Applicative_id :: Product FB FA A -> Property
prop_Product_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Product_Applicative_comp ::
    Product FB FA (Fun B C) -> Product FB FA (Fun A B) -> Product FB FA A ->
    Property
prop_Product_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Product_Applicative_homo :: Fun A B -> A -> Property
prop_Product_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @(Product FB FA)) f x))

prop_Product_Applicative_inter :: Product FB FA (Fun A B) -> A -> Property
prop_Product_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Compose_Applicative_id :: Compose FB FA A -> Property
prop_Compose_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Compose_Applicative_comp ::
    Compose FB FA (Fun B C) -> Compose FB FA (Fun A B) -> Compose FB FA A ->
    Property
prop_Compose_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Compose_Applicative_homo :: Fun A B -> A -> Property
prop_Compose_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @(Compose FB FA)) f x))

prop_Compose_Applicative_inter :: Compose FB FA (Fun A B) -> A -> Property
prop_Compose_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Const_Applicative_id :: Const M A -> Property
prop_Const_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Const_Applicative_comp ::
    Const M (Fun B C) -> Const M (Fun A B) -> Const M A -> Property
prop_Const_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Const_Applicative_homo :: Fun A B -> A -> Property
prop_Const_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @(Const M)) f x))

prop_Const_Applicative_inter :: Const M (Fun A B) -> A -> Property
prop_Const_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Maybe_Applicative_id :: Maybe A -> Property
prop_Maybe_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Maybe_Applicative_comp ::
    Maybe (Fun B C) -> Maybe (Fun A B) -> Maybe A -> Property
prop_Maybe_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Maybe_Applicative_homo :: Fun A B -> A -> Property
prop_Maybe_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @Maybe) f x))

prop_Maybe_Applicative_inter :: Maybe (Fun A B) -> A -> Property
prop_Maybe_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



newtype Small1 a = Small1 a
    deriving (Eq, Ord, Read, Show, Prelude.Functor)
instance Arbitrary a => Arbitrary (Small1 a) where
    arbitrary = Small1 Prelude.<$> scale (`div` 10) arbitrary
    shrink (Small1 x) = Small1 Prelude.<$> shrink x


prop_List_Applicative_id :: [A] -> Property
prop_List_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_List_Applicative_comp ::
    Small1 [Fun B C] -> Small1 [Fun A B] -> Small1 [A] -> Property
prop_List_Applicative_comp (Small1 gs') (Small1 fs') (Small1 xs) =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_List_Applicative_homo :: Fun A B -> A -> Property
prop_List_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @[]) f x))

prop_List_Applicative_inter :: [Fun A B] -> A -> Property
prop_List_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_ZipList_Applicative_id :: ZipList A -> Property
prop_ZipList_Applicative_id xs =
    let (ZipList us, ZipList vs) = getEqual (law_Applicative_id xs)
    in take 100 us === take 100 vs

prop_ZipList_Applicative_comp ::
    Small1 (ZipList (Fun B C)) -> Small1 (ZipList (Fun A B)) ->
    Small1 (ZipList A) -> Property
prop_ZipList_Applicative_comp (Small1 gs') (Small1 fs') (Small1 xs) =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_ZipList_Applicative_homo :: Fun A B -> A -> Property
prop_ZipList_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @[]) f x))

prop_ZipList_Applicative_inter :: ZipList (Fun A B) -> A -> Property
prop_ZipList_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
        (ZipList us, ZipList vs) = getEqual (law_Applicative_inter fs x)
    in take 100 us === take 100 vs
