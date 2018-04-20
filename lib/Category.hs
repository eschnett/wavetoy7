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
    , type (-#>)(..)
    ) where

import Prelude hiding (id, (.), curry, uncurry)
import qualified Prelude

import Data.Constraint
import Data.Kind
import Data.Void



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
class (Category k, CatProd (Prod k)) => Cartesian k where
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
class (Category k, CatCoprod (Coprod k)) => Cocartesian k where
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
newtype (-#>) a b = NFun { unNFun :: (Num a, Num b) => a -> b }

instance Category (-#>) where
    type Obj (-#>) = Num
    id = NFun id
    NFun g . NFun f = NFun (g . f)
    apply = unNFun
    unapply = NFun
