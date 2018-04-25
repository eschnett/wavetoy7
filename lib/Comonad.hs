module Comonad
    ( Comonad(..)
    , law_Comonad_extract
    , law_Comonad_duplicate
    , law_Comonad_extend
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )

import Data.Functor.Identity
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.List.NonEmpty

import Category
import Functor



-- | Comonad
class (Functor f, Cod f ~ Dom f) => Comonad f where
    {-# MINIMAL extract, (extend | duplicate)  #-}
    extract :: Obj (Dom f) a => f a -> a
    extend :: (Obj (Dom f) a, Obj (Dom f) b) => (f a -> b) -> f a -> f b
    default extend :: (Dom f ~ (->), Obj (Dom f) a, Obj (Dom f) b)
                      => (f a -> b) -> f a -> f b
    extend f = fmap f . duplicate
    duplicate :: (Obj (Dom f) a, Obj (Dom f) (f a)) => f a -> f (f a)
    duplicate = extend id

-- extract . fmap f = f . extract
law_Comonad_extract :: (Dom f ~ (->), Comonad f, Obj (Dom f) a, Obj (Dom f) b)
                       => Dom f a b -> FnEqual (f a) b
law_Comonad_extract f = (extract . fmap f) `fnEqual` (f . extract)

-- duplicate = extend id
law_Comonad_duplicate :: (Dom f ~ (->), Comonad f, Obj (Dom f) a)
                         => FnEqual (f a) (f (f a))
law_Comonad_duplicate = duplicate `fnEqual` extend id

-- extend f = fmap f . duplicate
law_Comonad_extend :: (Dom f ~ (->), Comonad f, Obj (Dom f) a, Obj (Dom f) b)
                      => Dom f (f a) b -> FnEqual (f a) (f b)
law_Comonad_extend f = extend f `fnEqual` (fmap f . duplicate)



instance Comonad Identity where
    extract (Identity x) = x
    extend f xs = Identity (f xs)

instance Comonad ((,) a) where
    extract (_, x) = x
    extend f xs@(a, x) = (a, f xs)

instance (Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ (->))
        => Comonad (F.Sum f g) where
    extract (InL xs) = extract xs
    extract (InR ys) = extract ys
    extend f (InL xs) = InL (extend (f . InL) xs)
    extend f (InR ys) = InR (extend (f . InR) ys)

instance (Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ (->))
        => Comonad (F.Product f g) where
    extract (Pair xs ys) = extract xs
    extend f (Pair xs ys) = Pair
                            (extend (\xs' -> f (Pair xs' ys)) xs)
                            (extend (\ys' -> f (Pair xs ys')) ys)

instance Comonad NonEmpty where
    extract (x :| _) = x
    extend f w@(x :| xs) = f w :| case xs of
                                    [] -> []
                                    y : ys -> let r :| rs = extend f (y :| ys)
                                              in r : rs
