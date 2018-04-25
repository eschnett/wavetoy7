{-# LANGUAGE UndecidableInstances #-}

module Functor
    ( Functor(..)
    , law_Functor_id
    , law_Functor_assoc
    , NList(..)
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      )

import Control.Applicative (ZipList(..))
import Data.Constraint
import Data.Functor.Compose as F
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.List.NonEmpty
import Data.Proxy
import qualified Test.QuickCheck as QC

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
        => Functor (F.Sum f g) where
    type Dom (F.Sum f g) = Dom f
    type Cod (F.Sum f g) = Cod f
    proveCod = Sub Dict
    fmap f (F.InL xs) = F.InL (fmap f xs)
    fmap f (F.InR ys) = F.InR (fmap f ys)

-- TODO: Relax 'Cod f ~ (->)'
instance (Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->))
        => Functor (F.Product f g) where
    type Dom (F.Product f g) = Dom f
    type Cod (F.Product f g) = Cod f
    proveCod = Sub Dict
    fmap f (Pair xs ys) = F.Pair (fmap f xs) (fmap f ys)

-- TODO: Relax 'Cod f ~ (->), Cod g ~ (->)'
instance (Functor f, Functor g, Dom f ~ Cod g, Cod f ~ (->), Cod g ~ (->))
        => Functor (F.Compose f g) where
    type Dom (F.Compose f g) = Dom g
    type Cod (F.Compose f g) = Cod f
    proveCod = Sub Dict
    fmap f (F.Compose xss) = F.Compose (fmap (fmap f) xss)

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

instance Functor NonEmpty where
    type Dom NonEmpty = Dom []
    type Cod NonEmpty = Cod []
    proveCod = Sub Dict
    fmap f (x :| xs) = f x :| fmap f xs

instance Functor ZipList where
    type Dom ZipList = Dom []
    type Cod ZipList = Cod []
    proveCod = Sub Dict
    fmap f (ZipList xs) = ZipList (fmap f xs)



newtype NList a = NList [a]
    deriving (Eq, Ord, Read, Show, QC.Arbitrary, QC.Arbitrary1)

instance Functor NList where
    type Dom NList = (-#>)
    type Cod NList = (->)
    proveCod = Sub Dict
    fmap f (NList xs) = NList (fmap (apply f) xs)
