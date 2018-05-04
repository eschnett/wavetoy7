{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -O -fplugin GHC.Proof.Plugin #-}
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
import GHC.Proof hiding ((===))
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

proof_Proxy_Functor_id :: Obj (Dom Proxy) a => Proxy a -> Proof
proof_Proxy_Functor_id xs = proof (fmap id xs) (id xs)
-- proof_Proxy_Functor_id xs = uncurry proof (getFnEqual law_Functor_id xs)

proof_Proxy_Functor_assoc ::
    (Obj (Dom Proxy) a, Obj (Dom Proxy) b, Obj (Dom Proxy) c)
    => (b -> c) -> (a -> b) -> Proxy a -> Proof
proof_Proxy_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)
-- proof_Proxy_Functor_assoc g f xs =
--     uncurry proof (getFnEqual (law_Functor_assoc g f) xs)



prop_Identity_Functor_id :: Identity A -> Property
prop_Identity_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Identity_Functor_assoc :: Fun B C -> Fun A B -> Identity A -> Property
prop_Identity_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

proof_Identity_Functor_id :: Obj (Dom Identity) a => Identity a -> Proof
proof_Identity_Functor_id xs = proof (fmap id xs) (id xs)

proof_Identity_Functor_assoc ::
    (Obj (Dom Identity) a, Obj (Dom Identity) b, Obj (Dom Identity) c)
    => (b -> c) -> (a -> b) -> Identity a -> Proof
proof_Identity_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_Either_Functor_id :: Either B A -> Property
prop_Either_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Either_Functor_assoc :: Fun B C -> Fun A B -> Either B A -> Property
prop_Either_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

proof_Either_Functor_id :: Obj (Dom (Either b)) a => Either b a -> Proof
proof_Either_Functor_id xs = proof (fmap id xs) (id xs)

proof_Either_Functor_assoc ::
    (Obj (Dom (Either d)) a, Obj (Dom (Either d)) b, Obj (Dom (Either d)) c)
    => (b -> c) -> (a -> b) -> Either d a -> Proof
proof_Either_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_Tuple_Functor_id :: (B, A) -> Property
prop_Tuple_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Tuple_Functor_assoc :: Fun B C -> Fun A B -> (B, A) -> Property
prop_Tuple_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

proof_Tuple_Functor_id :: Obj (Dom ((,) b)) a => (b, a) -> Proof
proof_Tuple_Functor_id xs = proof (fmap id xs) (id xs)

proof_Tuple_Functor_assoc ::
    (Obj (Dom ((,) d)) a, Obj (Dom ((,) d)) b, Obj (Dom ((,) d)) c)
    => (b -> c) -> (a -> b) -> (d, a) -> Proof
proof_Tuple_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_Function_Functor_id :: Fun B A -> NonEmptyList B -> Property
prop_Function_Functor_id (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual law_Functor_id xs
    in conjoin [u b === v b | b <- bs]

prop_Function_Functor_assoc ::
    Fun B C -> Fun A B -> Fun B A -> NonEmptyList B -> Property
prop_Function_Functor_assoc (Fn g) (Fn f) (Fn xs) (NonEmpty bs) =
    let (u, v) = getFnEqual (law_Functor_assoc g f) xs
    in conjoin [u b === v b | b <- bs]

-- proof_Function_Functor_id :: (B -> A) -> Proof
-- proof_Function_Functor_id xs = proof (fmap id xs) (id xs)
proof_Function_Functor_id :: Obj (Dom ((->) b)) a => (b -> a) -> b -> Proof
proof_Function_Functor_id xs y = proof (fmap id xs y) (id xs y)

proof_Function_Functor_assoc ::
    (Obj (Dom ((->) d)) a, Obj (Dom ((->) d)) b, Obj (Dom ((->) d)) c)
    => (b -> c) -> (a -> b) -> (d -> a) -> Proof
proof_Function_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



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

-- proof_Sum_Functor_id ::
--     ( Functor f, Functor g, Cod f ~ (->), Cod g ~ Cod f, Dom g ~ Dom f
--     , Obj (Dom (Sum f g)) a
--     ) => Sum f g a -> Proof
-- proof_Sum_Functor_id xs = proof (fmap id xs) (id xs)
-- 
-- proof_Sum_Functor_assoc ::
--     ( Functor f, Functor g
--     , Cod f ~ (->), Cod g ~ Cod f, Dom f ~ (->), Dom g ~ Dom f
--     , Obj (Dom (Sum f g)) a
--     ) => (b -> c) -> (a -> b) -> Sum f g a -> Proof
-- proof_Sum_Functor_assoc g f xs =
--     proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_Product_Functor_id :: Product FB FA A -> Property
prop_Product_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Product_Functor_assoc :: Fun B C -> Fun A B -> Product FB FA A -> Property
prop_Product_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

-- proof_Product_Functor_id ::
--     ( Functor f, Functor g, Cod f ~ (->), Cod g ~ Cod f, Dom g ~ Dom f
--     , Obj (Dom (Product f g)) a
--     ) => Product f g a -> Proof
-- proof_Product_Functor_id xs = proof (fmap id xs) (id xs)
-- 
-- proof_Product_Functor_assoc ::
--     ( Functor f, Functor g
--     , Cod f ~ (->), Cod g ~ Cod f, Dom f ~ (->), Dom g ~ Dom f
--     , Obj (Dom (Product f g)) a
--     ) => (b -> c) -> (a -> b) -> Product f g a -> Proof
-- proof_Product_Functor_assoc g f xs =
--     proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



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

proof_Const_Functor_id :: Obj (Dom (Const b)) a => Const b a -> Proof
proof_Const_Functor_id xs = proof (fmap id xs) (id xs)

proof_Const_Functor_assoc ::
    (Obj (Dom (Const d)) a, Obj (Dom (Const d)) b, Obj (Dom (Const d)) c)
    => (b -> c) -> (a -> b) -> Const d a -> Proof
proof_Const_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_Maybe_Functor_id :: Maybe A -> Property
prop_Maybe_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_Maybe_Functor_assoc :: Fun B C -> Fun A B -> Maybe A -> Property
prop_Maybe_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

proof_Maybe_Functor_id :: Obj (Dom Maybe) a => Maybe a -> Proof
proof_Maybe_Functor_id xs = proof (fmap id xs) (id xs)

proof_Maybe_Functor_assoc ::
    (Obj (Dom Maybe) a, Obj (Dom Maybe) b, Obj (Dom Maybe) c)
    => (b -> c) -> (a -> b) -> Maybe a -> Proof
proof_Maybe_Functor_assoc g f xs =
    proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_List_Functor_id :: [A] -> Property
prop_List_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_List_Functor_assoc :: Fun B C -> Fun A B -> [A] -> Property
prop_List_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

-- proof_List_Functor_id :: Obj (Dom []) a => [a] -> Proof
-- proof_List_Functor_id xs = proof (fmap id xs) (id xs)
-- 
-- proof_List_Functor_assoc ::
--     (Obj (Dom []) a, Obj (Dom []) b, Obj (Dom []) c)
--     => (b -> c) -> (a -> b) -> [a] -> Proof
-- proof_List_Functor_assoc g f xs =
--     proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_NonEmpty_Functor_id :: NonEmpty A -> Property
prop_NonEmpty_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_NonEmpty_Functor_assoc :: Fun B C -> Fun A B -> NonEmpty A -> Property
prop_NonEmpty_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

-- proof_NonEmpty_Functor_id :: Obj (Dom NonEmpty) a => NonEmpty a -> Proof
-- proof_NonEmpty_Functor_id xs = proof (fmap id xs) (id xs)
-- 
-- proof_NonEmpty_Functor_assoc ::
--     (Obj (Dom NonEmpty) a, Obj (Dom NonEmpty) b, Obj (Dom NonEmpty) c)
--     => (b -> c) -> (a -> b) -> NonEmpty a -> Proof
-- proof_NonEmpty_Functor_assoc g f xs =
--     proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



prop_ZipList_Functor_id :: ZipList A -> Property
prop_ZipList_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_ZipList_Functor_assoc :: Fun B C -> Fun A B -> ZipList A -> Property
prop_ZipList_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc g f) xs)

-- proof_ZipList_Functor_id :: Obj (Dom ZipList) a => ZipList a -> Proof
-- proof_ZipList_Functor_id xs = proof (fmap id xs) (id xs)
-- 
-- proof_ZipList_Functor_assoc ::
--     (Obj (Dom ZipList) a, Obj (Dom ZipList) b, Obj (Dom ZipList) c)
--     => (b -> c) -> (a -> b) -> ZipList a -> Proof
-- proof_ZipList_Functor_assoc g f xs =
--     proof (fmap (g . f) xs) ((fmap g . fmap f) xs)



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



prop_NList_Functor_id :: NList NA -> Property
prop_NList_Functor_id xs =
    uncurry (===) (getFnEqual law_Functor_id xs)

prop_NList_Functor_assoc :: Fun NB NC -> Fun NA NB -> NList NA -> Property
prop_NList_Functor_assoc (Fn g) (Fn f) xs =
    uncurry (===) (getFnEqual (law_Functor_assoc (NFun g) (NFun f)) xs)

-- proof_NList_Functor_id :: Obj (Dom NList) a => NList a -> Proof
-- proof_NList_Functor_id xs = proof (fmap id xs) (id xs)
-- 
-- proof_NList_Functor_assoc ::
--     (Obj (Dom NList) a, Obj (Dom NList) b, Obj (Dom NList) c)
--     => (b -> c) -> (a -> b) -> NList a -> Proof
-- proof_NList_Functor_assoc g' f' xs =
--     proof (fmap (g . f) xs) ((fmap g . fmap f) xs)
--     where f = NFun f'
--           g = NFun g'
