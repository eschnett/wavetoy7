{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -O -fplugin GHC.Proof.Plugin #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ApplicativeSpec where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Applicative(..), (<$>)
                      )
import qualified Prelude

import Data.Constraint
import Data.Functor.Classes
import Data.Functor.Compose as F
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.List.NonEmpty hiding (take)
import Data.Monoid hiding ((<>))
import Data.Proxy
import Data.Semigroup
import GHC.Proof hiding ((===))
import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Applicative
import Category
import Functor



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

prop_Proxy_Applicative_id' :: Fun A B -> Proxy A -> Property
prop_Proxy_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' f xs))

prop_Proxy_Applicative_id_left' :: Fun (A, B) C -> A -> Proxy B -> Property
prop_Proxy_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' f x ys))

prop_Proxy_Applicative_id_right' :: Fun (A, B) C -> Proxy A -> B -> Property
prop_Proxy_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' f xs y))

prop_Proxy_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Small1 (Proxy A) -> Small1 (Proxy B) -> Small1 (Proxy C) -> Property
prop_Proxy_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc' f g h i xs ys zs))

proof_Proxy_Applicative_id :: Proxy A -> Proof
proof_Proxy_Applicative_id xs =
    proof u v where (u, v) = getEqual (law_Applicative_id xs)

proof_Proxy_Applicative_comp ::
    Proxy (Fun B C) -> Proxy (Fun A B) -> Proxy A -> Proof
proof_Proxy_Applicative_comp gs' fs' xs =
    proof u v where (u, v) = getEqual (law_Applicative_comp gs fs xs)
                    gs = applyFun <$> gs'
                    fs = applyFun <$> fs'

proof_Proxy_Applicative_homo :: Fun A B -> A -> Proof
proof_Proxy_Applicative_homo (Fn f) x =
    proof u v where (u, v) = getEqual (law_Applicative_homo (Proxy @Proxy) f x)

proof_Proxy_Applicative_inter :: Proxy (Fun A B) -> A -> Proof
proof_Proxy_Applicative_inter fs' x =
    proof u v where (u, v) = getEqual (law_Applicative_inter fs x)
                    fs = applyFun <$> fs'

proof_Proxy_Applicative_id' :: Fun A B -> Proxy A -> Proof
proof_Proxy_Applicative_id' (Fn f) xs =
    proof u v where (u, v) = getEqual (law_Applicative_id' f xs)

proof_Proxy_Applicative_id_left' :: Fun (A, B) C -> A -> Proxy B -> Proof
proof_Proxy_Applicative_id_left' (Fn f) x ys =
    proof u v where (u, v) = getEqual (law_Applicative_id_left' f x ys)

proof_Proxy_Applicative_id_right' :: Fun (A, B) C -> Proxy A -> B -> Proof
proof_Proxy_Applicative_id_right' (Fn f) xs y =
    proof u v where (u, v) = getEqual (law_Applicative_id_right' f xs y)

proof_Proxy_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Proxy A -> Proxy B -> Proxy C -> Proof
proof_Proxy_Applicative_assoc' (Fn f) (Fn g) (Fn h) (Fn i) xs ys zs =
    proof u v where (u, v) = getEqual (law_Applicative_assoc' f g h i xs ys zs)



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

proof_Identity_Applicative_id :: Identity A -> Proof
proof_Identity_Applicative_id xs =
    proof u v where (u, v) = getEqual (law_Applicative_id xs)

proof_Identity_Applicative_comp ::
    Identity (Fun B C) -> Identity (Fun A B) -> Identity A -> Proof
proof_Identity_Applicative_comp gs' fs' xs =
    proof u v where (u, v) = getEqual (law_Applicative_comp gs fs xs)
                    gs = applyFun <$> gs'
                    fs = applyFun <$> fs'

proof_Identity_Applicative_homo :: Fun A B -> A -> Proof
proof_Identity_Applicative_homo (Fn f) x =
    proof u v
        where (u, v) = getEqual (law_Applicative_homo (Proxy @Identity) f x)

proof_Identity_Applicative_inter :: Identity (Fun A B) -> A -> Proof
proof_Identity_Applicative_inter fs' x =
    proof u v where (u, v) = getEqual (law_Applicative_inter fs x)
                    fs = applyFun <$> fs'



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

proof_Either_Applicative_id :: Either B A -> Proof
proof_Either_Applicative_id xs =
    proof u v where (u, v) = getEqual (law_Applicative_id xs)

proof_Either_Applicative_comp ::
    Either B (Fun B C) -> Either B (Fun A B) -> Either B A -> Proof
proof_Either_Applicative_comp gs' fs' xs =
    proof u v where (u, v) = getEqual (law_Applicative_comp gs fs xs)
                    gs = applyFun <$> gs'
                    fs = applyFun <$> fs'

proof_Either_Applicative_homo :: Fun A B -> A -> Proof
proof_Either_Applicative_homo (Fn f) x =
    proof u v
        where (u, v) = getEqual (law_Applicative_homo (Proxy @(Either B)) f x)

proof_Either_Applicative_inter :: Either B (Fun A B) -> A -> Proof
proof_Either_Applicative_inter fs' x =
    proof u v where (u, v) = getEqual (law_Applicative_inter fs x)
                    fs = applyFun <$> fs'



-- newtype M = M (Sum Integer)
newtype M = M (Sum Int)
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

proof_Tuple_Applicative_id :: (M, A) -> Proof
proof_Tuple_Applicative_id xs =
    proof u v where (u, v) = getEqual (law_Applicative_id xs)

proof_Tuple_Applicative_comp :: (M, Fun B C) -> (M, Fun A B) -> (M, A) -> Proof
proof_Tuple_Applicative_comp gs' fs' xs =
    proof u v where (u, v) = getEqual (law_Applicative_comp gs fs xs)
                    gs = applyFun <$> gs'
                    fs = applyFun <$> fs'

proof_Tuple_Applicative_homo :: Fun A B -> A -> Proof
proof_Tuple_Applicative_homo (Fn f) x =
    proof u v
        where (u, v) = getEqual (law_Applicative_homo (Proxy @((,) M)) f x)

proof_Tuple_Applicative_inter :: (M, Fun A B) -> A -> Proof
proof_Tuple_Applicative_inter fs' x =
    proof u v where (u, v) = getEqual (law_Applicative_inter fs x)
                    fs = applyFun <$> fs'



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



prop_Product_Applicative_id :: F.Product FB FA A -> Property
prop_Product_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Product_Applicative_comp ::
    F.Product FB FA (Fun B C) -> F.Product FB FA (Fun A B) ->
    F.Product FB FA A -> Property
prop_Product_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Product_Applicative_homo :: Fun A B -> A -> Property
prop_Product_Applicative_homo (Fn f) x =
    uncurry (===)
                (getEqual (law_Applicative_homo (Proxy @(F.Product FB FA)) f x))

prop_Product_Applicative_inter :: F.Product FB FA (Fun A B) -> A -> Property
prop_Product_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))



prop_Compose_Applicative_id :: F.Compose FB FA A -> Property
prop_Compose_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_Compose_Applicative_comp ::
    F.Compose FB FA (Fun B C) -> F.Compose FB FA (Fun A B) ->
    F.Compose FB FA A -> Property
prop_Compose_Applicative_comp gs' fs' xs =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_Compose_Applicative_homo :: Fun A B -> A -> Property
prop_Compose_Applicative_homo (Fn f) x =
    uncurry (===)
                (getEqual (law_Applicative_homo (Proxy @(Compose FB FA)) f x))

prop_Compose_Applicative_inter :: F.Compose FB FA (Fun A B) -> A -> Property
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

prop_Const_Applicative_id' :: Fun A B -> Const M A -> Property
prop_Const_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' f xs))

prop_Const_Applicative_id_left' :: Fun (A, B) C -> A -> Const M B -> Property
prop_Const_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' f x ys))

prop_Const_Applicative_id_right' :: Fun (A, B) C -> Const M A -> B -> Property
prop_Const_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' f xs y))

prop_Const_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Small1 (Const M A) -> Small1 (Const M B) -> Small1 (Const M C) -> Property
prop_Const_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc' f g h i xs ys zs))

proof_Const_Applicative_id :: Const M A -> Proof
proof_Const_Applicative_id xs =
    proof u v where (u, v) = getEqual (law_Applicative_id xs)

-- proof_Const_Applicative_comp ::
--     Const M (Fun B C) -> Const M (Fun A B) -> Const M A -> Proof
-- proof_Const_Applicative_comp gs' fs' xs =
--     proof u v where (u, v) = getEqual (law_Applicative_comp gs fs xs)
--                     gs = applyFun <$> gs'
--                     fs = applyFun <$> fs'

proof_Const_Applicative_homo :: Fun A B -> A -> Proof
proof_Const_Applicative_homo (Fn f) x =
    proof u v
        where (u, v) = getEqual (law_Applicative_homo (Proxy @(Const M)) f x)

-- proof_Const_Applicative_inter :: Const M (Fun A B) -> A -> Proof
-- proof_Const_Applicative_inter fs' x =
--     proof u v where (u, v) = getEqual (law_Applicative_inter fs x)
--                     fs = applyFun <$> fs'

proof_Const_Applicative_id' :: Fun A B -> Const M A -> Proof
proof_Const_Applicative_id' (Fn f) xs =
    proof u v where (u, v) = getEqual (law_Applicative_id' f xs)

proof_Const_Applicative_id_left' :: Fun (A, B) C -> A -> Const M B -> Proof
proof_Const_Applicative_id_left' (Fn f) x ys =
    proof u v where (u, v) = getEqual (law_Applicative_id_left' f x ys)

proof_Const_Applicative_id_right' :: Fun (A, B) C -> Const M A -> B -> Proof
proof_Const_Applicative_id_right' (Fn f) xs y =
    proof u v where (u, v) = getEqual (law_Applicative_id_right' f xs y)

-- proof_Const_Applicative_assoc' ::
--     Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
--     Const M A -> Const M B -> Const M C -> Proof
-- proof_Const_Applicative_assoc' (Fn f) (Fn g) (Fn h) (Fn i) xs ys zs =
--     proof u v where (u, v) = getEqual (law_Applicative_assoc' f g h i xs ys zs)



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

proof_Maybe_Applicative_id :: Maybe A -> Proof
proof_Maybe_Applicative_id xs =
    proof u v where (u, v) = getEqual (law_Applicative_id xs)

proof_Maybe_Applicative_comp ::
    Maybe (Fun B C) -> Maybe (Fun A B) -> Maybe A -> Proof
proof_Maybe_Applicative_comp gs' fs' xs =
    proof u v where (u, v) = getEqual (law_Applicative_comp gs fs xs)
                    gs = applyFun <$> gs'
                    fs = applyFun <$> fs'

proof_Maybe_Applicative_homo :: Fun A B -> A -> Proof
proof_Maybe_Applicative_homo (Fn f) x =
    proof u v
        where (u, v) = getEqual (law_Applicative_homo (Proxy @Maybe) f x)

proof_Maybe_Applicative_inter :: Maybe (Fun A B) -> A -> Proof
proof_Maybe_Applicative_inter fs' x =
    proof u v where (u, v) = getEqual (law_Applicative_inter fs x)
                    fs = applyFun <$> fs'



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

prop_List_Applicative_id' :: Fun A B -> [A] -> Property
prop_List_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' f xs))

prop_List_Applicative_id_left' :: Fun (A, B) C -> A -> [B] -> Property
prop_List_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' f x ys))

prop_List_Applicative_id_right' ::
    Fun (A, B) C -> [A] -> B -> Property
prop_List_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' f xs y))

prop_List_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Small1 [A] -> Small1 [B] -> Small1 [C] -> Property
prop_List_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc' f g h i xs ys zs))



prop_NonEmpty_Applicative_id :: NonEmpty A -> Property
prop_NonEmpty_Applicative_id xs =
    uncurry (===) (getEqual (law_Applicative_id xs))

prop_NonEmpty_Applicative_comp ::
    Small1 (NonEmpty (Fun B C)) -> Small1 (NonEmpty (Fun A B)) ->
    Small1 (NonEmpty A) -> Property
prop_NonEmpty_Applicative_comp (Small1 gs') (Small1 fs') (Small1 xs) =
    let gs = applyFun <$> gs'
        fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_comp gs fs xs))

prop_NonEmpty_Applicative_homo :: Fun A B -> A -> Property
prop_NonEmpty_Applicative_homo (Fn f) x =
    uncurry (===) (getEqual (law_Applicative_homo (Proxy @NonEmpty) f x))

prop_NonEmpty_Applicative_inter :: NonEmpty (Fun A B) -> A -> Property
prop_NonEmpty_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
    in uncurry (===) (getEqual (law_Applicative_inter fs x))

prop_NonEmpty_Applicative_id' :: Fun A B -> NonEmpty A -> Property
prop_NonEmpty_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' f xs))

prop_NonEmpty_Applicative_id_left' ::
    Fun (A, B) C -> A -> NonEmpty B -> Property
prop_NonEmpty_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' f x ys))

prop_NonEmpty_Applicative_id_right' ::
    Fun (A, B) C -> NonEmpty A -> B -> Property
prop_NonEmpty_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' f xs y))

prop_NonEmpty_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Small1 (NonEmpty A) -> Small1 (NonEmpty B) -> Small1 (NonEmpty C) ->
    Property
prop_NonEmpty_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc' f g h i xs ys zs))



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
    let (ZipList us, ZipList vs) =
            getEqual (law_Applicative_homo (Proxy @ZipList) f x)
    in take 100 us === take 100 vs

prop_ZipList_Applicative_inter :: ZipList (Fun A B) -> A -> Property
prop_ZipList_Applicative_inter fs' x =
    let fs = applyFun <$> fs'
        (ZipList us, ZipList vs) = getEqual (law_Applicative_inter fs x)
    in take 100 us === take 100 vs

prop_ZipList_Applicative_id' :: Fun A B -> ZipList A -> Property
prop_ZipList_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' f xs))

prop_ZipList_Applicative_id_left' ::
    Fun (A, B) C -> A -> ZipList B -> Property
prop_ZipList_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' f x ys))

prop_ZipList_Applicative_id_right' ::
    Fun (A, B) C -> ZipList A -> B -> Property
prop_ZipList_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' f xs y))

prop_ZipList_Applicative_assoc' ::
    Fun A A -> Fun B B -> Fun C C -> Fun (A, (B, C)) A ->
    Small1 (ZipList A) -> Small1 (ZipList B) -> Small1 (ZipList C) ->
    Property
prop_ZipList_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc' f g h i xs ys zs))



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



prop_NList_Applicative_id' :: Fun NA NB -> NList NA -> Property
prop_NList_Applicative_id' (Fn f) xs =
    uncurry (===) (getEqual (law_Applicative_id' (NFun f) xs))

prop_NList_Applicative_id_left' ::
    Fun (NA *.* NB) NC -> NA -> NList NB -> Property
prop_NList_Applicative_id_left' (Fn f) x ys =
    uncurry (===) (getEqual (law_Applicative_id_left' (NFun f) x ys))

prop_NList_Applicative_id_right' ::
    Fun (NA *.* NB) NC -> NList NA -> NB -> Property
prop_NList_Applicative_id_right' (Fn f) xs y =
    uncurry (===) (getEqual (law_Applicative_id_right' (NFun f) xs y))

prop_NList_Applicative_assoc' ::
    Fun NA NA -> Fun NB NB -> Fun NC NC -> Fun (NA *.* (NB *.* NC)) NA ->
    Small1 (NList NA) -> Small1 (NList NB) -> Small1 (NList NC) -> Property
prop_NList_Applicative_assoc'
        (Fn f) (Fn g) (Fn h) (Fn i) (Small1 xs) (Small1 ys) (Small1 zs) =
    uncurry (===) (getEqual (law_Applicative_assoc'
                             (NFun f) (NFun g) (NFun h) (NFun i) xs ys zs))
