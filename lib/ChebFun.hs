{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ChebFun
    ( ChebVal()
    , ChebFun(..)
    , compactify, uncompactify, clamp
    , law_ChebFun_compact_inv
    , law_ChebFun_compact_inv'
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      , Applicative(..), (<$>)
                      )

import Control.Exception (assert)
import Data.Constraint
import GHC.Generics
import qualified Test.QuickCheck as QC

import Applicative
import Category
import Chebyshev
import Foldable
import qualified Function as F
import Functor
import Unbox
import Unfoldable



-- | ChebVal
class (RealFloat a, Obj (Dom v) a) => ChebVal v a
instance (RealFloat a, Obj (Dom v) a) => ChebVal v a

instance F.MCategory (ChebVal v)



-- | ChebFun
newtype ChebFun v a b = ChebFun { getChebFun :: v b }
    deriving ( Eq, Ord, Show, Generic
             , QC.Arbitrary, QC.CoArbitrary
             )

instance (Functor v, Cod v ~ (->)) => Functor (ChebFun v a) where
    type Dom (ChebFun v a) = Dom v
    type Cod (ChebFun v a) = Cod v
    proveCod = Sub Dict
    fmap f (ChebFun xs) = ChebFun (fmap f xs)

instance (Applicative v, Cod v ~ (->)) => Applicative (ChebFun v a) where
    pure = ChebFun . pure
    ChebFun fs <*> ChebFun xs = ChebFun (fs <*> xs)
    liftA2 f (ChebFun xs) (ChebFun ys) = ChebFun (liftA2 f xs ys)
    liftA2' f (ChebFun xs, ChebFun ys) = ChebFun (liftA2' f (xs, ys))

instance Foldable v => F.Morphism (ChebFun v) where
    type Cat (ChebFun v) = ChebVal v
    chase (ChebFun cs) = chebyshev cs . realToFrac

instance (Foldable v, Sized v, Unfoldable v)
        => F.Discretization (ChebFun v) where
    discretize = ChebFun . chebyshevApprox (size @v)



clamp :: Ord a => a -> a -> a -> a
clamp lo hi = max lo . min hi

-- | input: \( [-\infty, \infty] \),
--   output: \( [-1; 1] \)
compactify :: RealFloat a => a -> a
compactify x = let y = 2 / pi * atan x
               in assert (-1 <= y && y <= 1) y

uncompactify :: RealFloat a => a -> a
uncompactify y =
    assert (-1 <= y && y <= 1) $
    tan (pi / 2 * clamp (-1) 1 y)

-- | prop> uncompactify . compactify = id
law_ChebFun_compact_inv :: RealFloat a => FnEqual a a
law_ChebFun_compact_inv = (uncompactify . compactify) `fnEqual` id @(->)

-- | prop> compactify . uncompactify = id
law_ChebFun_compact_inv' :: RealFloat a => FnEqual a a
law_ChebFun_compact_inv' =
    (compactify . uncompactify) `fnEqual` id @(->)
