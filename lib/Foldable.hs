module Foldable
    ( Foldable(..)
    , concat, concatMap
    , product
    , maximum, minimum
    , and, or
    , all, any
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      , concat, concatMap, sum, product, maximum, minimum
                      , and, or, all, any
                      )

import Control.Applicative (ZipList(..))
-- import Data.Constraint
import Data.Functor.Compose as F
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.List.NonEmpty hiding (length, toList)
import Data.Monoid hiding (First(..))
import Data.Proxy
import GHC.Base (build)

import Category
import Functor



-- | Foldable
class Functor f => Foldable f where
    {-# MINIMAL foldMap | foldr #-}
    fold :: (k ~ Dom f, Obj k a, Monoid a) => f a -> a
    {-# INLINE fold #-}
    fold = foldMap id
    foldMap :: forall k a b.
               (k ~ Dom f, Obj k a, Obj k b, Monoid b) =>
               a `k` b -> f a -> b
    -- foldMap f = fold . apply (fmap f)
    --             \\ (proveCod :: Obj k a :- Obj (Cod f) (f a))
    --             \\ (proveCod :: Obj k b :- Obj (Cod f) (f b))
    {-# INLINE foldMap #-}
    default foldMap :: forall k a b.
                       (Dom f ~ (->), k ~ Dom f, Obj k a, Obj k b, Monoid b)
                       => a `k` b -> f a -> b
    foldMap f = foldr (mappend . f) mempty
    foldr :: (k ~ Dom f, Obj k a) => (a -> b -> b) -> b -> f a -> b
    {-# INLINE foldr #-}
    default foldr :: (Dom f ~ (->), k ~ Dom f, Obj k a)
                     => (a -> b -> b) -> b -> f a -> b
    foldr f z xs = appEndo (foldMap (Endo . f) xs) z
    foldl :: (k ~ Dom f, Obj k b) => (a -> b -> a) -> a -> f b -> a
    {-# INLINE foldl #-}
    default foldl :: (Dom f ~ (->), k ~ Dom f, Obj k b)
                     => (a -> b -> a) -> a -> f b -> a
    foldl f z xs = appEndo (getDual (foldMap (Dual . Endo . flip f) xs)) z

    null :: (k ~ Dom f, Obj k a) => f a -> Bool
    {-# INLINE null #-}
    default null :: (Dom f ~ (->), k ~ Dom f, Obj k a) => f a -> Bool
    null = getAll . foldMap (All . const False)
    length :: (k ~ Dom f, Obj k a) => f a -> Int
    {-# INLINE length #-}
    default length :: (Dom f ~ (->), k ~ Dom f, Obj k a) => f a -> Int
    length = getSum . foldMap (Sum . const 1)
    elem :: (k ~ Dom f, Obj k a, Eq a) => a -> f a -> Bool
    {-# INLINE elem #-}
    default elem :: (Dom f ~ (->), k ~ Dom f, Obj k a, Eq a) => a -> f a -> Bool
    elem x = getAny . foldMap (Any . (== x))
    toList :: (k ~ Dom f, Obj k a, Obj (Dom []) a) => f a -> [a]
    {-# INLINE toList #-}
    default toList :: (Dom f ~ (->), k ~ Dom f, Obj k a) => f a -> [a]
    toList = foldMap (:[])
    -- toList xs = build (\f z -> foldr f z xs)

    {-# INLINE sum #-}
    sum :: (Foldable f, k ~ Dom f, Obj k a, Num a) => f a -> a
    sum = foldr (+) 0

concat :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a) => f [a] -> [a]
concat xs = build (\c z -> foldr (\x y -> foldr c y x) z xs)

concatMap :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a)
             => a `k` [b] -> f a -> [b]
concatMap f xs = build (\c z -> foldr (\x b -> foldr c b (f x)) z xs)

-- {-# INLINE sum #-}
-- sum :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a, Num a) => f a -> a
-- sum = getSum . foldMap Sum
-- sum :: (Foldable f, k ~ Dom f, Obj k a, Num a) => f a -> a
-- sum = foldr (+) 0

product :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a, Num a) => f a -> a
product = getProduct . foldMap Product

-- {-# INLINE maximum #-}
-- maximum :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a, Bounded a, Ord a)
--            => f a -> a
-- maximum = getMax . foldMap Max
maximum :: (Foldable f, k ~ Dom f, Obj k a, Bounded a, Ord a) => f a -> a
maximum = foldr max minBound

-- {-# INLINE minimum #-}
-- minimum :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a, Bounded a, Ord a)
--            => f a -> a
-- minimum = getMin . foldMap Min
minimum :: (Foldable f, k ~ Dom f, Obj k a, Bounded a, Ord a) => f a -> a
minimum = foldr min maxBound

and :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k Bool) => f Bool -> Bool
and = getAll . foldMap All

or :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k Bool) => f Bool -> Bool
or = getAny . foldMap Any

all :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a)
       => a `k` Bool -> f a -> Bool
all p = getAll . foldMap (All . p)

any :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a)
       => a `k` Bool -> f a -> Bool
any p = getAny . foldMap (Any . p)

-- find :: (Foldable f, Dom f ~ (->), k ~ Dom f, Obj k a)
--        => a `k` Bool -> f a -> Maybe a
-- find p = getFirst . foldMap (\x -> First (if p x then Just x else Nothing))



instance Foldable Proxy where
    foldMap _ Proxy = mempty

instance Foldable Identity where
    foldMap f (Identity x) = f x

instance Foldable (Either a) where
    foldMap f (Left _) = mempty
    foldMap f (Right x) = f x

instance Foldable ((,) a) where
    foldMap f (_, x) = f x

instance (Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
        => Foldable (F.Sum f g) where
    foldMap f (InL xs) = foldMap f xs
    foldMap f (InR ys) = foldMap f ys
    foldr f z (InL xs) = foldr f z xs
    foldr f z (InR ys) = foldr f z ys
    foldl f z (InL xs) = foldl f z xs
    foldl f z (InR ys) = foldl f z ys
    null (InL xs) = null xs
    null (InR ys) = null ys
    length (InL xs) = length xs
    length (InR ys) = length ys
    elem x (InL xs) = elem x xs
    elem x (InR ys) = elem x ys
    toList (InL xs) = toList xs
    toList (InR ys) = toList ys
    sum (InL xs) = sum xs
    sum (InR ys) = sum ys

instance (Foldable f, Foldable g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
        => Foldable (F.Product f g) where
    foldMap f (Pair xs ys) = foldMap f xs `mappend` foldMap f ys
    foldr f z (Pair xs ys) = foldr f (foldr f z ys) xs
    foldl f z (Pair xs ys) = foldl f (foldl f z xs) ys
    null (Pair xs ys) = null xs && null ys
    length (Pair xs ys) = length xs + length ys
    elem x (Pair xs ys) = elem x xs || elem x ys
    toList (Pair xs ys) = toList xs ++ toList ys
    sum (Pair xs ys) = sum xs + sum ys

instance (Foldable f, Foldable g, Dom f ~ Cod g, Cod f ~ (->), Cod g ~ (->))
        => Foldable (F.Compose f g) where
    foldMap f (Compose xss) = foldMap (foldMap f) xss
    foldr f z (Compose xss) = foldr (\xs r -> foldr f r xs) z xss
    foldl f z (Compose xss) = foldl (foldl f) z xss
    null (Compose xss) = all null xss
    length (Compose xss) = sum (fmap length xss)
    -- length (Compose xss) = getSum (foldMap (Sum . length) xss)
    elem x (Compose xss) = any (elem x) xss
    toList (Compose xss) = concatMap toList xss
    sum (Compose xss) = sum (fmap sum xss)

instance Foldable (Const a) where
    foldMap _ (Const _) = mempty

instance Foldable Maybe where
    foldMap _ Nothing = mempty
    foldMap f (Just x) = f x

instance Foldable [] where
    foldMap _ [] = mempty
    foldMap f (x:xs) = f x `mappend` foldMap f xs

instance Foldable NonEmpty where
    foldMap f (x :| xs) = f x `mappend` foldMap f xs

instance Foldable ZipList where
    foldMap f (ZipList xs) = foldMap f xs
