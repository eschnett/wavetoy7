module Unfoldable (Unfoldable(..)) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )

import Control.Applicative (ZipList(..))
-- import Data.Functor.Compose as F
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.List.NonEmpty hiding (unfoldr)
import Data.Proxy

import Category
import Comonoid
import Functor



-- | Unfoldable
-- (this uses the State monad)
class Functor f => Unfoldable f where
    -- {-# MINIMAL mapUnfold | unfoldr #-}
    unfold :: (k ~ Dom f, Obj k a, Comonoid a) => a -> (a, f a)
    unfold = mapUnfold id
    mapUnfold :: (k ~ Dom f, Obj k b, Comonoid a) => (a -> b) -> a -> (a, f b)
    mapUnfold f = unfoldr counit (\y -> let (y1, y2) = split y in (f y1, y2))
    unfoldr :: (k ~ Dom f, Obj k b)
               => (a -> Bool) -> (a -> (b, a)) -> a -> (a, f b)
    -- unfoldr c s x = getCoendo ... Coendo ...
    fromList :: (k ~ Dom f, Obj k a, Obj (Dom []) a) => [a] -> Maybe (f a)
    -- TODO: This is broken since head is partial
    -- fromList = Just . mapUnfold head



instance Unfoldable Proxy where
    mapUnfold _ x = (x, Proxy)
    unfoldr _ _ x = (x, Proxy)
    fromList _ = Just Proxy

instance Unfoldable Identity where
    mapUnfold f x = let (x1, x2) = split x in (x2, Identity (f x1))
    unfoldr c s x = let (y, x') = s x in (x', Identity y)

instance Monoid a => Unfoldable (Either a) where
    mapUnfold f x = if counit x
                    then (x, Left mempty)
                    else let (x1, x2) = split x in (x2, Right (f x1))

instance Monoid a => Unfoldable ((,) a) where
    mapUnfold f x = let (x1, x2) = split x in (x2, (mempty, f x1))

instance ( Unfoldable f, Unfoldable g
         , Dom f ~ Dom g, Cod f ~ Cod g, Cod g ~ (->)
         ) => Unfoldable (F.Product f g) where
    mapUnfold f x = let (y, xs) = mapUnfold f x
                        (z, ys) = mapUnfold f y
                    in (z, Pair xs ys)

-- instance ( Unfoldable f, Unfoldable g
--          , Dom f ~ Dom g, Cod f ~ Cod g, Cod g ~ (->)
--          ) => Unfoldable (F.Compose f g) where

instance Monoid a => Unfoldable (Const a) where
    mapUnfold _ x = (x, Const mempty)

instance Unfoldable Maybe where
    mapUnfold f x = if counit x
                    then (x, Nothing)
                    else let (x1, x2) = split x in (x2, Just (f x1))

instance Unfoldable [] where
    mapUnfold f x = if counit x
                    then (x, [])
                    else let (x1, x2) = split x
                         in fmap (f x1 :) (mapUnfold f x2)

instance Unfoldable NonEmpty where
    mapUnfold f x = let (x1, x') = split x
                        (x'', y2) = mapUnfold f x'
                    in (x'', f x1 :| y2)

instance Unfoldable ZipList where
    mapUnfold f x = fmap ZipList (mapUnfold f x)
