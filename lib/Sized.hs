module Sized
    ( intVal
    , Sized(..)
    ) where

import Data.Kind
import Data.Proxy
import GHC.TypeLits



-- | Use as 'intVal @n'
intVal :: forall n. KnownNat n => Int
intVal = fromInteger (natVal (Proxy @n))

class KnownNat (Size v) => Sized (v :: Type -> Type) where
    type Size v :: Nat
    size :: Int
    size = intVal @(Size v)
