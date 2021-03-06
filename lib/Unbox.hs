{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Unbox
    ( Unbox
    , type (-#>)(..)
    , type (*#*)(..)
    , UUnit(..)
    , Indexed(..)
    , intVal
    , Sized(..)
    , WithSize(..)
    , Pointed(..)
    , Copointed(..)
    , WithPointer(..)
    , NVVector
    , NUVector
    , CNVVector
    , CNUVector
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      , Applicative(..), (<$>)
                      )
import qualified Prelude

import Data.Constraint
import Data.Maybe
import Data.Monoid
import qualified Data.Vector as V
import Data.Vector.Unboxed (Unbox)
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving
import GHC.Generics
import GHC.TypeLits
import qualified Test.QuickCheck as QC
import Test.QuickCheck.Instances()

import Applicative
import Category
import Comonad
import Foldable
import Functor
import Sized
import Unfoldable



-- | Unbox is a category
newtype (-#>) a b = UFun { unUFun :: (Unbox a, Unbox b) => a -> b }

newtype (*#*) a b = UProd { getUProd :: (a, b) }
    deriving (Eq, Ord, Read, Show, Generic)

instance QC.Arbitrary (a, b) => QC.Arbitrary (a *#* b) where
    arbitrary = UProd Prelude.<$> QC.arbitrary
    shrink p = UProd Prelude.<$> QC.shrink (getUProd p)
instance (QC.CoArbitrary a, QC.CoArbitrary b) => QC.CoArbitrary (a *#* b)
instance (QC.Function a, QC.Function b) => QC.Function (a *#* b)

derivingUnbox "UProd"
    [t| forall a b. (Unbox a, Unbox b) => a *#* b -> (a, b) |]
    [| getUProd |]
    [| UProd |]

newtype UUnit = UUnit ()
    deriving (Eq, Ord, Read, Show, Generic)

instance QC.Arbitrary UUnit where
    arbitrary = UUnit Prelude.<$> QC.arbitrary
    shrink _ = UUnit Prelude.<$> QC.shrink ()
instance QC.CoArbitrary UUnit
instance QC.Function UUnit

derivingUnbox "UUnit"
    [t| UUnit -> () |]
    [| const () |]
    [| UUnit |]



instance Category (-#>) where
    type Obj (-#>) = Unbox
    {-# INLINE id #-}
    id = UFun id
    {-# INLINE (.) #-}
    UFun g . UFun f = UFun (g . f)
    {-# INLINE apply #-}
    apply = unUFun
    {-# INLINE unapply #-}
    unapply = UFun

instance CatProd (*#*) where
    type ProdCat (*#*) = (-#>)
    type Unit (*#*) = UUnit
    {-# INLINE punit #-}
    punit = UUnit ()
    {-# INLINE prod #-}
    prod = UProd
    {-# INLINE unprod #-}
    unprod = getUProd

instance Cartesian (-#>) where
    type Prod (-#>) = (*#*)
    {-# INLINE proveCartesian #-}
    proveCartesian = Sub Dict



instance QC.Function a => QC.Function (V.Vector a) where
    function = QC.functionMap V.toList V.fromList

instance (QC.Function a, Unbox a) => QC.Function (U.Vector a) where
    function = QC.functionMap U.toList U.fromList

instance Functor V.Vector where
    type Dom V.Vector = (->)
    type Cod V.Vector = (->)
    {-# INLINE proveCod #-}
    proveCod = Sub Dict
    {-# INLINE fmap #-}
    fmap = V.map

instance Functor U.Vector where
    type Dom U.Vector = (-#>)
    type Cod U.Vector = (->)
    proveCod = Sub Dict
    {-# INLINE fmap #-}
    fmap f = U.map (apply f)

instance Foldable V.Vector where
    {-# INLINE foldMap #-}
    foldMap f = V.foldl (\r x -> r <> f x) mempty
    {-# INLINE foldr #-}
    foldr = V.foldr
    {-# INLINE foldl #-}
    foldl = V.foldl
    {-# INLINE sum #-}
    sum = V.sum

instance Foldable U.Vector where
    {-# INLINE foldMap #-}
    foldMap f = U.foldl (\r x -> r <> f `apply` x) mempty
    {-# INLINE foldr #-}
    foldr = U.foldr
    {-# INLINE foldl #-}
    foldl = U.foldl
    {-# INLINE null #-}
    null = U.null
    {-# INLINE length #-}
    length = U.length
    {-# INLINE elem #-}
    elem x = U.any (x ==)
    {-# INLINE toList #-}
    toList = U.toList
    {-# INLINE sum #-}
    sum = U.sum

instance Unfoldable V.Vector where
    unfoldr c s x = let (ys, x') = unfoldr c s x
                    in (fromJust (fromList ys), x')
    fromList = Just . V.fromList

instance Unfoldable U.Vector where
    unfoldr c s x = let (ys, x') = unfoldr c s x
                    in (fromJust (fromList ys), x')
    fromList = Just . U.fromList

class Functor v => Indexed v where
    index :: Obj (Dom v) a => v a -> Int -> a

instance Indexed V.Vector where
    index = (V.!)

instance Indexed U.Vector where
    index = (U.!)



newtype WithSize (n :: Nat) v a = WithSize (v a)
    deriving Generic

deriving instance Eq (v a) => Eq (WithSize n v a)
deriving instance Ord (v a) => Ord (WithSize n v a)
deriving instance Show (v a) => Show (WithSize n v a)

instance ( QC.Arbitrary a, Foldable v, Unfoldable v, Obj (Dom v) a
         , KnownNat n
         ) => QC.Arbitrary (WithSize n v a) where
    arbitrary = [ WithSize (fromJust (fromList xs))
                | xs <- QC.vector (intVal @n)]
    shrink (WithSize xs) = [ WithSize (fromJust (fromList xs'))
                           | xs' <- QC.shrink (toList xs)
                           , length xs' == intVal @n]
-- instance (QC.Arbitrary a, KnownNat n)
--         => QC.Arbitrary (WithSize n V.Vector a) where
--     arbitrary = [ WithSize (V.fromListN (intVal @n) xs)
--                 | xs <- QC.vector (intVal @n)]
--     shrink (WithSize xs) = [ WithSize (V.fromListN (intVal @n) xs')
--                            | xs' <- QC.shrink (V.toList xs)
--                            , length xs' == intVal @n]
-- instance (QC.Arbitrary a, Unbox a, KnownNat n)
--         => QC.Arbitrary (WithSize n U.Vector a) where
--     arbitrary = [ WithSize (U.fromListN (intVal @n) xs)
--                 | xs <- QC.vector (intVal @n)]
--     shrink (WithSize xs) = [ WithSize (U.fromListN (intVal @n) xs')
--                            | xs' <- QC.shrink (U.toList xs)
--                            , length xs' == intVal @n]
instance QC.CoArbitrary (v a) => QC.CoArbitrary (WithSize n v a)
instance QC.Function (v a) => QC.Function (WithSize n v a)

instance (Indexed v, Cod v ~ (->)) => Indexed (WithSize n v) where
    index (WithSize xs) = index xs

instance KnownNat n => Sized (WithSize n v) where
    type Size (WithSize n v) = n

instance (Functor v, Cod v ~ (->)) => Functor (WithSize n v) where
    type Dom (WithSize n v) = Dom v
    type Cod (WithSize n v) = (->)
    proveCod = Sub Dict
    {-# INLINE fmap #-}
    fmap f (WithSize xs) = WithSize (fmap f xs)

instance (Foldable v, Cod v ~ (->)) => Foldable (WithSize n v) where
    {-# INLINE foldMap #-}
    foldMap f (WithSize xs) = foldMap f xs
    {-# INLINE foldr #-}
    foldr f z (WithSize xs) = foldr f z xs
    {-# INLINE foldl #-}
    foldl f z (WithSize xs) = foldl f z xs
    {-# INLINE null #-}
    null (WithSize xs) = null xs
    {-# INLINE length #-}
    length (WithSize xs) = length xs
    {-# INLINE elem #-}
    elem x (WithSize xs) = elem x xs
    {-# INLINE toList #-}
    toList (WithSize xs) = toList xs
    {-# INLINE sum #-}
    sum (WithSize xs) = sum xs

instance (Unfoldable v, Cod v ~ (->)) => Unfoldable (WithSize n v) where
    unfoldr c s x = let (r, x') = unfoldr c s x in (WithSize r, x')
    fromList xs = WithSize <$> fromList xs

instance KnownNat n => Applicative (WithSize n V.Vector) where
    {-# INLINE pure #-}
    pure x = WithSize (V.replicate (intVal @n) x)
    {-# INLINE liftA2 #-}
    liftA2 f (WithSize xs) (WithSize ys) = WithSize (V.zipWith f xs ys)

instance KnownNat n => Applicative (WithSize n U.Vector) where
    {-# INLINE pure #-}
    pure x = WithSize (U.replicate (intVal @n) x)
    (<*>) = undefined
    {-# INLINE liftA2' #-}
    liftA2' f (WithSize xs, WithSize ys) =
        WithSize (U.zipWith (\x y -> f `apply` UProd (x, y)) xs ys)



class Functor p => Pointed p where
    point :: Obj (Dom f) a => a -> p a

class Functor p => Copointed p where
    copoint :: Obj (Dom p) a => p a -> a

data WithPointer v a = WithPointer !Int !(v a)
                       deriving Generic

deriving instance Eq (v a) => Eq (WithPointer v a)
deriving instance Ord (v a) => Ord (WithPointer v a)
deriving instance Show (v a) => Show (WithPointer v a)

instance (QC.Arbitrary (v a), Foldable v, Obj (Dom v) a)
        => QC.Arbitrary (WithPointer v a) where
    arbitrary = do xs <- QC.arbitrary
                   i <- QC.choose (0, length xs - 1)
                   return (WithPointer i xs)
    shrink (WithPointer i xs) = [ WithPointer i' xs'
                                | (i', xs') <- QC.shrink (i, xs)
                                , i' >= 0 && i' < length xs']
instance QC.CoArbitrary (v a) => QC.CoArbitrary (WithPointer v a)
instance QC.Function (v a) => QC.Function (WithPointer v a)

instance (Indexed v, Cod v ~ (->)) => Indexed (WithPointer v) where
    index (WithPointer _ xs) i = index xs i

instance Sized v => Sized (WithPointer v) where
    type Size (WithPointer v) = Size v

instance (Indexed v, Cod v ~ (->)) => Copointed (WithPointer v) where
    copoint (WithPointer i xs) = index xs i

instance (Functor v, Cod v ~ (->)) => Functor (WithPointer v) where
    type Dom (WithPointer v) = Dom v
    type Cod (WithPointer v) = (->)
    proveCod = Sub Dict
    {-# INLINE fmap #-}
    fmap f (WithPointer i xs) = WithPointer i (fmap f xs)

instance (Foldable v, Cod v ~ (->)) => Foldable (WithPointer v) where
    {-# INLINE foldMap #-}
    foldMap f (WithPointer _ xs) = foldMap f xs
    {-# INLINE foldr #-}
    foldr f z (WithPointer _ xs) = foldr f z xs
    {-# INLINE foldl #-}
    foldl f z (WithPointer _ xs) = foldl f z xs
    {-# INLINE null #-}
    null (WithPointer _ xs) = null xs
    {-# INLINE length #-}
    length (WithPointer _ xs) = length xs
    {-# INLINE elem #-}
    elem x (WithPointer _ xs) = elem x xs
    {-# INLINE toList #-}
    toList (WithPointer _ xs) = toList xs
    {-# INLINE sum #-}
    sum (WithPointer _ xs) = sum xs

instance (Unfoldable v, Cod v ~ (->)) => Unfoldable (WithPointer v) where
    unfoldr c s x = let (r, x') = unfoldr c s x in (WithPointer 0 r, x')
    fromList xs = WithPointer 0 <$> fromList xs

instance (Applicative v, Cod v ~ (->), 1 <= Size v)
        => Applicative (WithPointer v) where
    {-# INLINE pure #-}
    pure x = WithPointer 0 (pure x)
    {-# INLINE (<*>) #-}
    WithPointer i fs <*> WithPointer j xs = WithPointer (max i j) (fs <*> xs)
    {-# INLINE liftA2 #-}
    liftA2 f (WithPointer i xs) (WithPointer j ys) =
        WithPointer (max i j) (liftA2 f xs ys)
    {-# INLINE liftA2' #-}
    liftA2' f (WithPointer i xs, WithPointer j ys) =
        WithPointer (max i j) (liftA2' f (xs, ys))



type NVVector (n :: Nat) = WithSize n V.Vector
type NUVector (n :: Nat) = WithSize n U.Vector
type CNVVector (n :: Nat) = WithPointer (WithSize n V.Vector)
type CNUVector (n :: Nat) = WithPointer (WithSize n U.Vector)



instance KnownNat n => Comonad (CNVVector n) where
    extract = copoint
    extend f (WithPointer i xs) =
        WithPointer i (WithSize (V.generate (intVal @n) gen))
            where gen j = f `apply` WithPointer j xs

instance KnownNat n => Comonad (CNUVector n) where
    extract = copoint
    extend f (WithPointer i (WithSize xs)) =
        WithPointer i (WithSize (U.generate (intVal @n) gen))
            where gen j = f `apply` WithPointer j (WithSize xs)
