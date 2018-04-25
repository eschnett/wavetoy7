module Comonoid ( Cosemigroup(..)
                , law_Cosemigroup_inv
                , Comonoid(..)
                , law_Comonoid_counit
                , law_Comonoid_inv
                -- , Coendo(..)
                , Counter(..)
                , CountDown(..)
                , Counted(..)
                , Forever(..)
                ) where

import Data.Bifunctor
import Data.Monoid hiding ((<>))
import Data.Proxy
import Data.Semigroup

import Category



class Cosemigroup w where
    split1 :: w -> Maybe (w, w)
    default split1 :: Comonoid w => w -> Maybe (w, w)
    split1 w = if counit w then Nothing else Just (split w)

-- If there is a Semigroup, then it must be the converse of the Cosemigroup
law_Cosemigroup_inv :: (Cosemigroup w, Semigroup w) => w -> Equal w
law_Cosemigroup_inv x =
    x `equal` case split1 x of
                Nothing -> x
                (Just (y, z)) -> y <> z



class Cosemigroup w => Comonoid w where
    -- In a 'Comonad', this is 'extract'
    -- destroy :: w -> ()
    counit :: w -> Bool
    default counit :: Eq w => w -> Bool
    counit w = split w == (w, w)
    -- In a 'Comonad', this is 'duplicate'
    -- We could have both 'lsplit' and 'rsplit', akin to 'foldl' and
    -- 'foldr'. Here, we expect 'rsplit' behaviour.
    split :: w -> (w, w)

-- 'counit' must be true for and only for a unit element
law_Comonoid_counit :: (Comonoid w, Eq w) => w -> Equal Bool
law_Comonoid_counit w = counit w `equal` (split w == (w, w))

-- If there is a Monoid, then it must be the converse of the Comonoid
law_Comonoid_inv :: (Comonoid w, Semigroup w) => w -> Equal w
law_Comonoid_inv x = x `equal` (let (y, z) = split x in y <> z)

-- The Semigroup associativity implies co-associativity for the Cosemigroup



-- Main rules:
-- - Don't define a Cosemigroup that is never splittable
-- - Don't define a Cosemigroup that is trivially based on a Monoid

instance Cosemigroup ()
instance Comonoid () where
    counit () = True
    split () = ((), ())

instance Cosemigroup (Proxy a)
instance Comonoid (Proxy a) where
    counit Proxy = True
    split Proxy = (Proxy, Proxy)

instance Cosemigroup (Maybe a)
instance Comonoid (Maybe a) where
    counit Nothing = True
    counit (Just x) = False
    split Nothing = (Nothing, Nothing)
    split (Just x) = (Just x, Nothing)

-- Either is not a Monoid. (Then why is it a Semigroup?)
-- instance Monoid a => Cosemigroup (Either a b)
-- instance Monoid a => Comonoid (Either a b) where
--     counit (Left x) = True
--     counit (Right y) = False
--     split xs = (xs, Left mempty)

instance (Cosemigroup a, Cosemigroup b) => Cosemigroup (a, b) where
    split1 (x, y) =
        case (split1 x, split1 y) of
          (Just (x1, x2), Just (y1, y2)) -> Just ((x1, y1), (x2, y2))
          _ -> Nothing
instance (Comonoid a, Comonoid b) => Comonoid (a, b) where
    counit (x, y) = counit x && counit y
    split (x, y) = let (x1, x2) = split x
                       (y1, y2) = split y
                   in ((x1, y1), (x2, y2))

instance Cosemigroup [a]
instance Comonoid [a] where
    counit = null
    split [] = ([], [])
    split (x:xs) = ([x], xs)



instance (Num a, Ord a) => Cosemigroup (Sum a)
instance (Num a, Ord a) => Comonoid (Sum a) where
    split (Sum x) = if | x > 0 -> (Sum 1, Sum (x - 1))
                       | x < 0 -> (Sum (-1), Sum (x + 1))
                       | otherwise -> (Sum 0, Sum x)



-- data Coendo a b = Coendo { counit_ :: a -> Bool
--                          , split_ :: a -> (b, a)
--                          , getCoendo :: a
--                          }
-- instance Cosemigroup (Coendo a b)
-- instance Comonoid (Coendo a b) where
--     counit (Coendo c s x) = c x
--     split (Coendo c s x) = let (y, x') = s x in (Coendo _, Coendo c s x')



newtype Counter = Counter { getCounter :: Int }
    deriving (Eq, Ord, Read, Show)
instance Cosemigroup Counter
instance Comonoid Counter where
    counit (Counter n) = False
    split (Counter n) = (Counter n, Counter (n + 1))

newtype CountDown = CountDown { getCountDown :: Int }
    deriving (Eq, Ord, Read, Show)
instance Cosemigroup CountDown
instance Comonoid CountDown where
    counit (CountDown n) = n == 0
    split (CountDown n) = (CountDown n, CountDown (n - 1))

data Counted a = Counted { getCount :: Int, getCounted :: a }
                 deriving (Eq, Ord, Read, Show)
instance Comonoid a => Cosemigroup (Counted a)
instance Comonoid a => Comonoid (Counted a) where
    counit (Counted n x) = counit (Sum n)
    split (Counted n x) =
        let (Sum n1, Sum n2) = split (Sum n)
        in bimap (Counted n1) (Counted n2) (split x)

newtype Forever a = Forever { getForever :: a }
    deriving (Eq, Ord, Read, Show)
instance Comonoid a => Cosemigroup (Forever a)
instance Comonoid a => Comonoid (Forever a) where
    counit (Forever x) = False
    split (Forever x) = bimap Forever Forever (split x)

-- This is Data.List.NonEmpty.NonEmpty
-- data FromList a = FromList { getFromList :: a, getRemainingList :: [a] }
--     deriving (Eq, Ord, Read, Show)
-- instance Cosemigroup (FromList a) where
--     split1 (FromList x []) = Nothing
--     split1 (FromList x (y:ys)) = Just (FromList x [], FromList y ys)



data Tree a = Leaf a | Branch (Tree a) (Tree a)
              deriving (Eq, Ord, Read, Show)
instance Cosemigroup (Tree a) where
    split1 (Leaf x) = Nothing
    split1 (Branch l r) = Just (l, r)
