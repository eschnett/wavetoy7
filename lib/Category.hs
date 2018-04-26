{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Category
    ( Equal(..)
    , equal
    , getEqual
    , FnEqual(..)
    , fnEqual
    , getFnEqual
    , CatKind
    , Category(..)
    , law_Category_comp_id_left
    , law_Category_comp_id_right
    , law_Category_comp_assoc
    , CatProd(..)
    , Cartesian(..)
    , CatCoprod(..)
    , Cocartesian(..)
    , Closed(..)
    , Hask
    , type (-.>)(..)
    , type (*.*)(..), NUnit(..)
    -- , type (+.+)(..), NCounit()
    ) where

import Prelude hiding (id, (.), curry, uncurry)
import qualified Prelude

import Data.Constraint
import Data.Kind
import Data.Void
import GHC.Generics
import qualified Test.QuickCheck as QC



-- | Equality
data Equal a = Equal a a
               deriving (Eq, Ord, Read, Show)
equal :: a -> a -> Equal a
equal = Equal
getEqual :: Equal a -> (a, a)
getEqual (Equal x y) = (x, y)

-- | Function equality
data FnEqual a b = FnEqual (a -> b) (a -> b)
fnEqual :: ( Category k, Obj k a, Obj k b
           , Category l, Obj l a, Obj l b)
           => a `k` b -> a `l` b -> FnEqual a b
fnEqual fx gx = FnEqual (apply fx) (apply gx)
getFnEqual :: FnEqual a b -> a -> (b, b)
getFnEqual (FnEqual fx gx) x = (fx x, gx x)



-- | Category
type CatKind = Type -> Type -> Type
type ObjKind = Type -> Constraint
class Category (k :: CatKind) where
    type Obj k :: ObjKind
    id :: Obj k a => a `k` a
    (.) :: (Obj k a, Obj k b, Obj k c) => b `k` c -> a `k` b -> a `k` c
    apply :: (Obj k a, Obj k b) => a `k` b -> a -> b
    unapply :: (Obj k a, Obj k b) => (a -> b) -> a `k` b

-- id . f = f
law_Category_comp_id_left :: (Category k, Obj k a, Obj k b)
                             => a `k` b -> FnEqual a b
law_Category_comp_id_left f = (id . f) `fnEqual` f

-- f . id = f
law_Category_comp_id_right :: (Category k, Obj k a, Obj k b)
                              => a `k` b -> FnEqual a b
law_Category_comp_id_right f = (f . id) `fnEqual` f

-- (h . g) . f = h . (g . f)
law_Category_comp_assoc :: (Category k, Obj k a, Obj k b, Obj k c, Obj k d)
                           => c `k` d -> b `k` c -> a `k` b -> FnEqual a d
law_Category_comp_assoc h g f = ((h . g) . f) `fnEqual` (h . (g . f))



-- | Cartesian category
type ProdKind = Type -> Type -> Type
class CatProd (p :: ProdKind) where
    type Unit p :: Type
    punit :: Unit p
    prod :: (a, b) -> p a b
    unprod :: p a b -> (a, b)
    -- punitLeft :: b -> p (Unit p) b
    -- punitRight :: a -> p a (Unit p)
    -- preunitLeft :: p (Unit p) b -> b
    -- preunitRight :: p a (Unit p) -> a
    -- punitLeft y = prod (punit, y)
    -- punitRight x = prod (x, punit)
    -- preunitLeft p = snd (unprod p)
    -- preunitRight p = fst (unprod p)
    -- passoc :: (Obj k a, Obj k b, Obj k c, p ~ Prod k)
    --           => p a (p b c) -> p (p a b) c
    -- preassoc :: (Obj k a, Obj k b, Obj k c, p ~ Prod k)
    --             => p (p a b) c -> p a (p b c)
    -- passoc p = let (x, q) = unprod p
    --                (y, z) = unprod q
    --            in prod (prod (x, y), z)
    -- preassoc p = let (q, z) = unprod p
    --                  (x, y) = unprod q
    --              in prod (x, prod (y, z))
class (Category k, CatProd (Prod k), Obj k (Unit (Prod k)))
        => Cartesian k where
    type Prod k :: ProdKind
    proveCartesian :: (Obj k a, Obj k b) :- Obj k (Prod k a b)

-- | Cocartesian category
type CoprodKind = Type -> Type -> Type
class CatCoprod (p :: CoprodKind) where
    type Counit p :: Type
    -- pcounit :: Counit p
    coprod :: Either a b -> p a b
    uncoprod :: p a b -> Either a b
    -- coassoc :: (Obj k a, Obj k b, Obj k c, p ~ Coprod k)
    --            => p a (p b c) -> p (p a b) c
    -- recoassoc :: (Obj k a, Obj k b, Obj k c, p ~ Coprod k)
    --              => p (p a b) c -> p a (p b c)
class (Category k, CatCoprod (Coprod k), Obj k (Counit (Coprod k)))
        => Cocartesian k where
    type Coprod k :: Type -> Type -> Type
    proveCocartesian :: (Obj k a, Obj k b) :- Obj k (Coprod k a b)

-- | Closed category
class Cartesian k => Closed k where
    proveClosed :: (Obj k a, Obj k b) :- Obj k (a `k` b)
    curry :: (Obj k a, Obj k b, Obj k c, p ~ Prod k)
             => p a b `k` c -> a `k` (b `k` c)
    uncurry :: (Obj k a, Obj k b, Obj k c, p ~ Prod k)
             => a `k` (b `k` c) -> p a b `k` c



-- | Hask
class Hask a
instance Hask a

instance Category (->) where
    type Obj (->) = Hask
    id = Prelude.id
    (.) = (Prelude..)
    apply = Prelude.id
    unapply = Prelude.id

instance CatProd (,) where
    type Unit (,) = ()
    punit = ()
    prod = id
    unprod = id
    -- assoc (x, (y, z)) = ((x, y), z)
    -- reassoc ((x, y), z) = (x, (y, z))
instance Cartesian (->) where
    type Prod (->) = (,)
    proveCartesian = Sub Dict

instance CatCoprod Either where
    type Counit Either = Void
    coprod = id
    uncoprod = id
    -- coassoc (Left x) = Left (Left x)
    -- coassoc (Right (Left y)) = Left (Right y)
    -- coassoc (Right (Right z)) = Right z
    -- recoassoc (Left (Left x)) = Left x
    -- recoassoc (Left (Right y)) = Right (Left y)
    -- recoassoc (Right z) = Right (Right z)
instance Cocartesian (->) where
    type Coprod (->) = Either
    proveCocartesian = Sub Dict

instance Closed (->) where
    proveClosed = Sub Dict
    curry = Prelude.curry
    uncurry = Prelude.uncurry
 


-- | Num is a category
newtype (-.>) a b = NFun { unNFun :: (Num a, Num b) => a -> b }

data (*.*) a b = NProd a b
                 deriving (Eq, Ord, Read, Show, Generic)
instance QC.Arbitrary (a, b) => QC.Arbitrary (a *.* b) where
    arbitrary = prod Prelude.<$> QC.arbitrary
    shrink p = prod Prelude.<$> QC.shrink (unprod p)
instance (QC.CoArbitrary a, QC.CoArbitrary b) => QC.CoArbitrary (a *.* b)
instance QC.Function (a, b) => QC.Function (a *.* b) where
    function = QC.functionMap unprod prod

instance (Num a, Num b) => Num (a *.* b) where
    NProd x1 x2 + NProd y1 y2 = NProd (x1 + y1) (x2 + y2)
    NProd x1 x2 * NProd y1 y2 = NProd (x1 * y1) (x2 * y2)
    negate (NProd x y) = NProd (negate x) (negate y)
    abs (NProd x y) = NProd (abs x) (abs y)
    signum (NProd x y) = NProd (signum x) (signum y)
    fromInteger n = NProd (fromInteger n) (fromInteger n)

data NUnit = NUnit
             deriving (Eq, Ord, Read, Show, Generic)

instance QC.Arbitrary NUnit where
    arbitrary = return NUnit
    shrink NUnit = []
instance QC.CoArbitrary NUnit
instance QC.Function NUnit where
    function = QC.functionMap (const ()) (const NUnit)

instance Num NUnit where
    NUnit + NUnit = NUnit
    NUnit * NUnit = NUnit
    negate NUnit = NUnit
    abs NUnit = NUnit
    signum NUnit = NUnit
    fromInteger _ = NUnit

instance Category (-.>) where
    type Obj (-.>) = Num
    id = NFun id
    NFun g . NFun f = NFun (g . f)
    apply = unNFun
    unapply = NFun

instance CatProd (*.*) where
    type Unit (*.*) = NUnit
    punit = NUnit
    prod (a, b) = NProd a b
    unprod (NProd a b) = (a, b)

instance Cartesian (-.>) where
    type Prod (-.>) = (*.*)
    proveCartesian = Sub Dict

-- data (+.+) a b = NLeft a | NRight b
--                  deriving (Eq, Ord, Read, Show)
-- instance (Num a, Num b) => Num (a +.+ b) where
--     NLeft x + NLeft y = NLeft (x + y)
--     NRight x + NRight y = NRight (x + y)
--     NLeft x + _ = NLeft x
--     _ + NLeft y = NLeft y
--     NLeft x * NLeft y = NLeft (x * y)
--     NRight x * NRight y = NRight (x * y)
--     NLeft x * _ = NLeft x
--     _ * NLeft y = NLeft y
--     negate (NLeft x) = NLeft (negate x)
--     negate (NRight x) = NRight (negate x)
--     abs (NLeft x) = NLeft (abs x)
--     abs (NRight x) = NRight (abs x)
--     signum (NLeft x) = NLeft (signum x)
--     signum (NRight x) = NRight (signum x)
--     fromInteger n = NLeft (fromInteger n)
-- 
-- data NCounit
-- instance CatCoprod (+.+) where
--     type Counit (+.+) = NCounit
--     coprod (Left a) = NLeft a
--     coprod (Right b) = NRight b
--     uncoprod (NLeft a) = Left a
--     uncoprod (NRight b) = Right b
-- 
-- instance Cocartesian (-.>) where
--     type Coprod (-.>) = (+.+)
--     proveCocartesian = Sub Dict
