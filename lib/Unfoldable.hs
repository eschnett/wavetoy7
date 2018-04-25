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
    {-# MINIMAL unfoldr, fromList #-}
    unfold :: (k ~ Dom f, Obj k a, Comonoid a) => a -> (f a, a)
    unfold = mapUnfold id
    mapUnfold :: (k ~ Dom f, Obj k b, Comonoid a) => (a -> b) -> a -> (f b, a)
    mapUnfold f = unfoldr counit (\y -> let (y1, y2) = split y in (f y1, y2))
    unfoldr :: (k ~ Dom f, Obj k b)
               => (a -> Bool) -> (a -> (b, a)) -> a -> (f b, a)
    -- unfoldr c s x = getCoendo ... Coendo ...
    fromList :: (k ~ Dom f, Obj k a, Obj (Dom []) a) => [a] -> Maybe (f a)
    -- TODO: This is broken since head is partial
    -- fromList = Just . mapUnfold head



instance Unfoldable Proxy where
    unfoldr _ _ x = (Proxy, x)
    fromList [] = Just Proxy
    fromList _ = Nothing

instance Unfoldable Identity where
    unfoldr c s x = let (y, x') = s x in (Identity y, x')
    fromList [x] = Just (Identity x)
    fromList _ = Nothing

instance Monoid a => Unfoldable (Either a) where
    unfoldr c s x = if c x
                    then (Left mempty, x)
                    else let (y, x') = s x in (Right y, x')
    fromList [] = Just (Left mempty)
    fromList [x] = Just (Right x)
    fromList _ = Nothing

instance Monoid a => Unfoldable ((,) a) where
    unfoldr c s x = let (y, x') = s x in ((mempty, y), x')
    fromList [x] = Just (mempty, x)
    fromList _ = Nothing

instance ( Unfoldable f, Unfoldable g
         , Dom f ~ Dom g, Cod f ~ Cod g, Cod g ~ (->)
         ) => Unfoldable (F.Product f g) where
    unfoldr c s x = let (xs, x') = unfoldr c s x
                        (ys, x'') = unfoldr c s x'
                    in (Pair xs ys, x'')

-- instance ( Unfoldable f, Unfoldable g
--          , Dom f ~ Dom g, Cod f ~ Cod g, Cod g ~ (->)
--          ) => Unfoldable (F.Compose f g) where

instance Monoid a => Unfoldable (Const a) where
    unfoldr _ _ x = (Const mempty, x)
    fromList [] = Just (Const mempty)
    fromList _ = Nothing

instance Unfoldable Maybe where
    unfoldr c s x = if c x
                    then (Nothing, x)
                    else let (y, x') = s x in (Just y, x')
    fromList [] = Just Nothing
    fromList [x] = Just (Just x)
    fromList _ = Nothing

instance Unfoldable [] where
    unfoldr c s x = if c x
                    then ([], x)
                    else let (y, x') = s x
                             (ys, x'') = unfoldr c s x'
                         in (y : ys, x'')
    fromList = Just

instance Unfoldable NonEmpty where
    unfoldr c s x = let (y, x') = s x
                        (ys, x'') = unfoldr c s x'
                    in (y :| ys, x'')
    fromList (x : xs) = Just (x :| xs)
    fromList _ = Nothing

instance Unfoldable ZipList where
    unfoldr c s x = let (y, x') = unfoldr c s x in (ZipList y, x')
    fromList = Just . ZipList
