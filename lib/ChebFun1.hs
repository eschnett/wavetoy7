{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module ChebFun1
    ( ChebVal()
    , ChebFun(..)
    -- , zeroCF, constCF, idCF
    , compactify, uncompactify, clamp
    , law_ChebFun_compact_inv
    , law_ChebFun_compact_inv'
    , ChebProd(..), ChebUnit(..)
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Foldable(..)
                      , Applicative(..), (<$>)
                      )
-- import qualified Prelude as P

import Control.Exception (assert)
import Data.Constraint
-- import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving
import GHC.Generics
import GHC.TypeLits
import qualified Test.QuickCheck as QC

import Applicative
import Category
import Chebyshev
-- import Foldable
import Functor
-- import Unfoldable
import Unbox



class (RealFloat a, Unbox a) => ChebVal a
instance (RealFloat a, Unbox a) => ChebVal a

-- TODO: Make NUVector a parameter; use "Dom v in ChebVal definition"
-- TODO: Support rational numbers somehow
newtype ChebFun (n :: Nat) a b = ChebFun (NUVector n b)
    deriving ( Eq, Ord, Show, Generic
             , QC.Arbitrary, QC.CoArbitrary -- , QC.Function
             -- , P.Functor, P.Foldable
             -- , Functor
             , Applicative
             )

instance Functor (ChebFun n a) where
    type Dom (ChebFun n a) = Dom (NUVector n)
    type Cod (ChebFun n a) = Cod (NUVector n)
    proveCod = Sub Dict
    fmap f (ChebFun xs) = ChebFun (fmap f xs)

-- instance Foldable (ChebFun n a) where
--     foldMap f (ChebFun xs) = foldMap f xs
--     foldr f z (ChebFun xs) = foldr f z xs
--     foldl f z (ChebFun xs) = foldl f z xs
--     toList (ChebFun xs) = toList xs



-- zeroCF :: forall n a b. (KnownNat n, Unbox b, Num b) => ChebFun n a b
-- zeroCF = ChebFun (WithSize (U.replicate (intVal @n) 0))
-- 
-- constCF :: forall n a b. (KnownNat n, Unbox b, Num b, 1 <= n)
--            => b -> ChebFun n a b
-- constCF x = ChebFun (WithSize (U.fromListN (intVal @n)
--                                     ([x] ++ replicate (intVal @n - 1) 0)))
-- 
-- idCF :: forall n a. (KnownNat n, Unbox a, Num a, 2 <= n) => ChebFun n a a
-- idCF = ChebFun (WithSize (U.fromListN (intVal @n)
--                                ([0, 1] ++ replicate (intVal @n - 2) 0)))



clamp :: Ord a => a -> a -> a -> a
clamp lo hi = max lo . min hi

-- | input: \( [-\infty, \infty] \),
--   output: \( [-1; 1] \)
--
-- > compactify x
--
-- >>> uncompactivy . compactify
--
-- prop> uncompactivy . compactify = id
compactify :: RealFloat a => a -> a
compactify x = let y = 2 / pi * atan x
               in assert (-1 <= y && y <= 1) y

uncompactify :: RealFloat a => a -> a
uncompactify y =
    assert (-1 <= y && y <= 1) $
    -- assert (-1.1 <= y && y <= 1.1) $
    tan (pi / 2 * clamp (-1) 1 y)

law_ChebFun_compact_inv :: RealFloat a => FnEqual a a
law_ChebFun_compact_inv = (uncompactify . compactify) `fnEqual` id @(->)

law_ChebFun_compact_inv' :: RealFloat a => FnEqual a a
law_ChebFun_compact_inv' =
    (compactify . uncompactify) `fnEqual` id @(->)



instance KnownNat n => Category (ChebFun n) where
    type Obj (ChebFun n) = ChebVal
    -- TODO: do these better!
    id = unapply id
    g . f = unapply (apply g . apply f)
    -- | [-1; 1] -> [-\infty; \infty]
    apply (ChebFun cs) = chebyshev cs . realToFrac
    unapply = ChebFun . chebyshevApprox (intVal @n)
    -- | [-\infty; \infty] -> [-\infty; \infty]
    -- apply (ChebFun cs) = chebyshev cs . realToFrac . compactify
    -- unapply f = ChebFun . chebyshevApprox (intVal @n) $ f . uncompactify
    -- | [-1; 1] -> [-1; 1]
    -- apply (ChebFun cs) = compactify . chebyshev cs . realToFrac
    -- unapply f = ChebFun . chebyshevApprox (intVal @n) $ uncompactify . f



newtype ChebProd (n :: Nat) a b = ChebProd { getChebProd :: (a, b) }
    deriving ( Eq, Ord, Read, Show, Generic
             , QC.Arbitrary, QC.CoArbitrary
             -- , Functor, Foldable, Unfoldable, Applicative
             )

derivingUnbox "ChebProd"
    [t| forall n a b. (Unbox a, Unbox b) => ChebProd n a b -> (a, b) |]
    [| getChebProd |]
    [| ChebProd |]

bimap :: (a -> c) -> (b -> d) -> ChebProd n a b -> ChebProd n c d
bimap f g (ChebProd (x, y)) = ChebProd (f x, g y)

bipure :: a -> b -> ChebProd n a b
bipure x y = ChebProd (x, y)

biliftA2 :: (a -> c -> e) -> (b -> d -> f) ->
            ChebProd n a b -> ChebProd n c d -> ChebProd n e f
biliftA2 f g (ChebProd (x1, y1)) (ChebProd (x2, y2)) =
    ChebProd (f x1 x2, g y1 y2)

bifoldMap :: (a -> c) -> (b -> d) -> (c -> d -> e) -> ChebProd n a b -> e
bifoldMap f g op (ChebProd (x, y)) = f x `op` g y

instance (Num a, Num b) =>  Num (ChebProd n a b) where
    (+) = biliftA2 (+) (+)
    (*) = biliftA2 (*) (*)
    negate = bimap negate negate
    abs = bimap abs abs
    signum = bimap signum signum
    fromInteger i = bipure (fromInteger i) (fromInteger i)

instance (Fractional a, Fractional b) => Fractional (ChebProd n a b) where
    recip = bimap recip recip
    fromRational r = bipure (fromRational r) (fromRational r)

instance (Real a, Real b) => Real (ChebProd n a b) where
    toRational (ChebProd (x, _)) = toRational x

instance (RealFrac a, RealFrac b) => RealFrac (ChebProd n a b) where
    properFraction (ChebProd (x, _)) = undefined -- properFraction x

instance (Floating a, Floating b) => Floating (ChebProd n a b) where
    pi = bipure pi pi
    exp = bimap exp exp
    log = bimap log log
    sin = bimap sin sin
    cos = bimap cos cos
    asin = bimap asin asin
    acos = bimap acos acos
    atan = bimap atan atan
    sinh = bimap sinh sinh
    cosh = bimap cosh cosh
    asinh = bimap asinh asinh
    acosh = bimap acosh acosh
    atanh = bimap atanh atanh

instance (RealFloat a, RealFloat b) => RealFloat (ChebProd n a b) where
    floatRadix _ = 0
    floatDigits _ = 0
    floatRange _ = (0, 0)
    decodeFloat _ = (0, 0)
    encodeFloat i j = bipure (encodeFloat i j) (encodeFloat i j)
    isNaN = bifoldMap isNaN isNaN (||)
    isInfinite = bifoldMap isInfinite isInfinite (||)
    isDenormalized = bifoldMap isDenormalized isDenormalized (||)
    isNegativeZero = bifoldMap isNegativeZero isNegativeZero (||)
    isIEEE _ = False



newtype ChebUnit n = ChebUnit ()
    deriving ( Eq, Ord, Read, Show, Generic
             , QC.Arbitrary, QC.CoArbitrary
             )

derivingUnbox "ChebUnit"
    [t| forall n. ChebUnit n -> () |]
    [| const () |]
    [| ChebUnit |]

instance Num (ChebUnit n) where
    _ + _ = ChebUnit ()
    _ * _ = ChebUnit ()
    negate _ = ChebUnit ()
    abs _ = ChebUnit ()
    signum _ = ChebUnit ()
    fromInteger _ = ChebUnit ()

instance Fractional (ChebUnit n) where
    recip _ = ChebUnit ()
    fromRational _ = ChebUnit ()

instance Real (ChebUnit n) where
    toRational _ = 0

instance RealFrac (ChebUnit n) where
    properFraction _ = (0, ChebUnit ())

instance Floating (ChebUnit n) where
    pi = ChebUnit ()
    exp _ = ChebUnit ()
    log _ = ChebUnit ()
    sin _ = ChebUnit ()
    cos _ = ChebUnit ()
    asin _ = ChebUnit ()
    acos _ = ChebUnit ()
    atan _ = ChebUnit ()
    sinh _ = ChebUnit ()
    cosh _ = ChebUnit ()
    asinh _ = ChebUnit ()
    acosh _ = ChebUnit ()
    atanh _ = ChebUnit ()

instance RealFloat (ChebUnit n) where
    floatRadix _ = 0
    floatDigits _ = 0
    floatRange _ = (0, 0)
    decodeFloat _ = (0, 0)
    encodeFloat _ _ = ChebUnit ()
    isNaN _ = False
    isInfinite _ = False
    isDenormalized _ = False
    isNegativeZero _ = False
    isIEEE _ = False
    


instance (KnownNat n, 2 <= n) => CatProd (ChebProd n) where
    type ProdCat (ChebProd n) = ChebFun n
    type Unit (ChebProd n) = ChebUnit n
    punit = ChebUnit ()
    prod = ChebProd
    unprod = getChebProd

instance (KnownNat n, 2 <= n) => Cartesian (ChebFun n) where
    type Prod (ChebFun n) = ChebProd n
    proveCartesian = Sub Dict
