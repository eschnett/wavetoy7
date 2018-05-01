module Function
    ( FnEqual(..), fnEqual, getFnEqual
    , ObjKind
    , MorKind, Morphism(..), Discretization(..), Ok, MId(..), MComp(..), (.:.)
    , CatKind, MCategory(..)
    , law_MCategory_comp_id_left
    , law_MCategory_comp_id_right
    , law_MCategory_comp_assoc
    , type (-.>)(..)
    ) where

import Prelude
import qualified Prelude as P

import Data.Constraint
import Data.Kind
import qualified Data.Vector.Unboxed as U ()
import GHC.Generics
import GHC.TypeLits

import ChebFun
import Chebyshev
import Unbox



-- | Function equality
data FnEqual a b = FnEqual (a -> b) (a -> b)
fnEqual :: (Ok m a b, Ok n a b) => a `m` b -> a `n` b -> FnEqual a b
fnEqual fx gx = FnEqual (chase fx) (chase gx)
getFnEqual :: FnEqual a b -> a -> (b, b)
getFnEqual (FnEqual fx gx) x = (fx x, gx x)



-- | Objects
type ObjKind = Type -> Constraint



-- | Morphism
type MorKind = Type -> Type -> Type
class MCategory (Cat m) => Morphism (m :: MorKind) where
    type Cat m :: CatKind
    chase :: (Obj (Cat m) a, Obj (Cat m) b) => a `m` b -> a -> b

class Morphism m => Discretization m where
    discretize :: (Obj (Cat m) a, Obj (Cat m) b) => (a -> b) -> a `m` b

type Ok m a b = (Morphism m, Obj (Cat m) a, Obj (Cat m) b)

data MId (k :: CatKind) a b where
    MId :: MId k a a
deriving instance Eq (MId k a b)
deriving instance Ord (MId k a b)
deriving instance Show (MId k a b)

instance MCategory k => Morphism (MId k) where
    type Cat (MId k) = k
    chase MId = P.id

data MComp n m b a c = MComp (n b c) (m a b)
                       deriving (Eq, Ord, Read, Show, Generic)
infixr 9 .:.
(.:.) :: n b c -> m a b -> MComp n m b a c
(.:.) = MComp

instance (Morphism m, Morphism n, Cat m ~ Cat n, Obj (Cat m) b)
        => Morphism (MComp n m b) where
    type Cat (MComp n m b) = Cat m
    chase (MComp g f) = chase g . chase f



-- | MCategory
type CatKind = Type -> Constraint
class MCategory (k :: CatKind) where
    type Obj k :: ObjKind
    type Obj k = k



-- id . f = f
law_MCategory_comp_id_left :: Ok m a b => a `m` b -> FnEqual a b
law_MCategory_comp_id_left f = (MId .:. f) `fnEqual` f

-- f . id = f
law_MCategory_comp_id_right :: Ok m a b => a `m` b -> FnEqual a b
law_MCategory_comp_id_right f = (f .:. MId) `fnEqual` f

-- (h . g) . f = h . (g . f)
law_MCategory_comp_assoc :: ( Cat m ~ Cat n, Cat n ~ Cat o
                            , Ok m a b, Ok n b c, Ok o c d
                            ) => c `o` d -> b `n` c -> a `m` b -> FnEqual a d
law_MCategory_comp_assoc h g f = ((h .:. g) .:. f) `fnEqual` (h .:. (g .:. f))




-- | Hask
class Hask a
instance Hask a

instance MCategory Hask

instance Morphism (->) where
    type Cat (->) = Hask
    chase = id

instance Discretization (->) where
    discretize = id



-- | Num
instance MCategory Num

newtype (-.>) a b = NFun { getNFun :: a -> b }
    deriving Generic

instance Morphism (-.>) where
    type Cat (-.>) = Num
    chase = getNFun

instance Discretization (-.>) where
    discretize = NFun



-- | ChebVal
instance MCategory ChebVal

instance Morphism (ChebFun n) where
    type Cat (ChebFun n) = ChebVal
    chase (ChebFun cs) = chebyshev cs . realToFrac

instance KnownNat n => Discretization (ChebFun n) where
    discretize = ChebFun . chebyshevApprox (intVal @n)
