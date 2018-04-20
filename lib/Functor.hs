{-# LANGUAGE UndecidableInstances #-}

module Functor
    ( Functor(..)
    , law_Functor_id
    , law_Functor_assoc
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )

import Control.Applicative (ZipList(..))
import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy

import Category



-- | Functor
class (Category (Dom f), Category (Cod f)) => Functor f where
    {-# MINIMAL proveCod, fmap #-}
    type Dom f :: CatKind
    type Cod f :: CatKind
    proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a)
    fmap :: (Obj (Dom f) a, Obj (Dom f) b) => Dom f a b -> Cod f (f a) (f b)

-- fmap id = id
law_Functor_id :: forall f a. (Functor f, Obj (Dom f) a)
                  => FnEqual (f a) (f a)
law_Functor_id = fmap id `fnEqual` (id @(Cod f))
                 \\ (proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a))

-- fmap (f . g) = fmap f . fmap g
law_Functor_assoc :: forall f a b c.
                     (Functor f, Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c)
                     => Dom f b c -> Dom f a b -> FnEqual (f a) (f c)
law_Functor_assoc g f = (fmap (g . f) `fnEqual` (fmap g . fmap f))
                        \\ (proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a))
                        \\ (proveCod :: Obj (Dom f) b :- Obj (Cod f) (f b))
                        \\ (proveCod :: Obj (Dom f) c :- Obj (Cod f) (f c))



instance Functor Proxy where
    type Dom Proxy = (->)
    type Cod Proxy = (->)
    proveCod = Sub Dict
    fmap _ Proxy = Proxy

instance Functor Identity where
    type Dom Identity = (->)
    type Cod Identity = (->)
    proveCod = Sub Dict
    fmap f (Identity x) = Identity (f x)

instance Functor (Either a) where
    type Dom (Either a) = (->)
    type Cod (Either a) = (->)
    proveCod = Sub Dict
    fmap _ (Left a) = Left a
    fmap f (Right x) = Right (f x)

instance Functor ((,) a) where
    type Dom ((,) a) = (->)
    type Cod ((,) a) = (->)
    proveCod = Sub Dict
    fmap f (a, x) = (a, f x)

instance Functor ((->) a) where
    type Dom ((->) a) = (->)
    type Cod ((->) a) = (->)
    proveCod = Sub Dict
    fmap f fx = \x -> f (fx x)

-- TODO: Relax 'Cod f ~ (->)'
instance (Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
        => Functor (Sum f g) where
    type Dom (Sum f g) = Dom f
    type Cod (Sum f g) = Cod f
    proveCod = Sub Dict
    fmap f (InL xs) = InL (fmap f xs)
    fmap f (InR ys) = InR (fmap f ys)

-- TODO: Relax 'Cod f ~ (->)'
instance (Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
        => Functor (Product f g) where
    type Dom (Product f g) = Dom f
    type Cod (Product f g) = Cod f
    proveCod = Sub Dict
    fmap f (Pair xs ys) = Pair (fmap f xs) (fmap f ys)

-- TODO: Relax 'Cod f ~ (->), Cod g ~ (->)'
instance (Functor f, Functor g, Dom f ~ Cod g, Cod f ~ (->), Cod g ~ (->))
        => Functor (Compose f g) where
    type Dom (Compose f g) = Dom g
    type Cod (Compose f g) = Cod f
    proveCod = Sub Dict
    fmap f (Compose xss) = Compose (fmap (fmap f) xss)

instance Functor (Const a) where
    type Dom (Const a) = (->)
    type Cod (Const a) = (->)
    proveCod = Sub Dict
    fmap _ (Const a) = Const a

instance Functor Maybe where
    type Dom Maybe = (->)
    type Cod Maybe = (->)
    proveCod = Sub Dict
    fmap _ Nothing = Nothing
    fmap f (Just x) = Just (f x)

instance Functor [] where
    type Dom [] = (->)
    type Cod [] = (->)
    proveCod = Sub Dict
    fmap _ [] = []
    fmap f (x:xs) = f x : fmap f xs

instance Functor ZipList where
    type Dom ZipList = Dom []
    type Cod ZipList = Cod []
    proveCod = Sub Dict
    fmap f (ZipList xs) = ZipList (fmap f xs)
