module Comonad
    ( Comonad(..)
    , law_Comonad_extract
    , law_Comonad_duplicate
    , law_Comonad_extend
    , law_Comonad_id_right
    , law_Comonad_id_left
    , law_Comonad_assoc
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )

import Data.Constraint
import Data.Functor.Identity
-- import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.List.NonEmpty

import Category
import Functor



-- | Comonad
class Functor f => Comonad f where
    {-# MINIMAL extract, (extend | duplicate)  #-}
    extract :: Obj (Dom f) a => f a -> a
    extend :: (Obj (Dom f) a, Obj (Dom f) b) => (f a -> b) -> f a -> f b
    default extend ::
        (Cod f ~ Dom f, Dom f ~ (->), Obj (Dom f) a, Obj (Dom f) b)
        => (f a -> b) -> f a -> f b
    extend f = fmap f . duplicate
    duplicate :: (Cod f ~ Dom f, Obj (Dom f) a, Obj (Dom f) (f a))
                 => f a -> f (f a)
    duplicate = extend id

-- extract . fmap f = f . extract
law_Comonad_extract ::
    (Comonad f, Cod f ~ (->), Obj (Dom f) a, Obj (Dom f) b)
    => Dom f a b -> FnEqual (f a) b
law_Comonad_extract f = (extract . fmap f) `fnEqual` (apply f . extract)

-- duplicate = extend id
law_Comonad_duplicate ::
    (Comonad f, Cod f ~ Dom f, Dom f ~ (->), Obj (Dom f) a)
    => FnEqual (f a) (f (f a))
law_Comonad_duplicate = duplicate `fnEqual` extend id

-- extend f = fmap f . duplicate
law_Comonad_extend ::
    (Comonad f, Cod f ~ Dom f, Dom f ~ (->), Obj (Dom f) a, Obj (Dom f) b)
    => Dom f (f a) b -> FnEqual (f a) (f b)
law_Comonad_extend f = extend f `fnEqual` (fmap f . duplicate)

-- extend extract = id
law_Comonad_id_right ::
    forall f a. (Comonad f, Obj (Dom f) a) => FnEqual (f a) (f a)
law_Comonad_id_right =
    extend extract `fnEqual` id @(Cod f)
       \\ (proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a))

-- extract . extend f = f
law_Comonad_id_left ::
    (Comonad f, Obj (Dom f) a, Obj (Dom f) b) => (f a -> b) -> FnEqual (f a) b
law_Comonad_id_left f =
    (extract . extend f) `fnEqual` f

-- extend g . extend f = extend (g . extend f)
law_Comonad_assoc ::
    (Comonad f, Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c)
    => (f a -> b) -> (f b -> c) -> FnEqual (f a) (f c)
law_Comonad_assoc f g =
    (extend g . extend f) `fnEqual` extend (g . extend f)



instance Comonad Identity where
    extract (Identity x) = x
    extend f xs = Identity (f xs)

instance Comonad ((,) a) where
    extract (_, x) = x
    extend f xs@(a, x) = (a, f xs)

instance (Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
        => Comonad (F.Sum f g) where
    extract (InL xs) = extract xs
    extract (InR ys) = extract ys
    extend f (InL xs) = InL (extend (f . InL) xs)
    extend f (InR ys) = InR (extend (f . InR) ys)

-- instance (Comonad f, Comonad g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
--         => Comonad (F.Product f g) where
--     extract (Pair xs ys) = extract xs
--     extend f (Pair xs ys) = Pair
--                             (extend (\xs' -> f (Pair xs' ys)) xs)
--                             (extend (\ys' -> f (Pair xs ys')) ys)

instance Comonad NonEmpty where
    extract (x :| _) = x
    extend f w@(x :| xs) = f w :| case xs of
                                    [] -> []
                                    y : ys -> let r :| rs = extend f (y :| ys)
                                              in r : rs
