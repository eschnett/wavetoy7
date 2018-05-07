{-# LANGUAGE UndecidableInstances #-}

module Function
    ( FnEqual(..), fnEqual, getFnEqual
    , ObjKind
    , MorKind, Morphism(..), Discretization(..), Ok, MId(..), MComp(..), (.:.)
    , CatKind, MCategory(..)
    , law_MCategory_comp_id_left
    , law_MCategory_comp_id_right
    , law_MCategory_comp_assoc
    , MFunctor(..)
    , law_MFunctor_id
    , law_MFunctor_assoc
    , type (-.>)(..)
    , NList(..)
    ) where

import Prelude hiding (Functor(..))
import qualified Prelude as P

import Data.Constraint
import Data.Kind
import qualified Data.Vector.Unboxed as U ()
import GHC.Generics
import qualified Test.QuickCheck as QC



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

data MComp' k a b where
    MComp' :: forall m n a b c. (Cat m ~ Cat n, Ok m a b, Ok n b c)
              => n b c -> m a b -> MComp' (Cat m) a c
-- deriving instance Eq (MComp' k a b)
-- deriving instance Ord (MComp' k a b)
-- deriving instance Show (MComp' k a b)

instance MCategory k => Morphism (MComp' k) where
    type Cat (MComp' k) = k
    chase (MComp' g f) = chase g . chase f



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



-- | MFunctor
class ( MCategory (Dom f), MCategory (Cod f)
      , Morphism (Mor f), Cat (Mor f) ~ Cod f
      ) => MFunctor (f :: Type -> Type) where
    type Dom f :: CatKind
    type Cod f :: CatKind
    type Mor f :: MorKind
    proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a)
    fmap :: ( Morphism m, Cat m ~ Dom f, Ok m a b
            , n ~ Mor f
            ) => a `m` b -> f a `n` f b

-- fmap id = id
law_MFunctor_id :: forall f a. (MFunctor f, Obj (Dom f) a)
                   => FnEqual (f a) (f a)
law_MFunctor_id =
    fmap (MId :: MId (Dom f) a a) `fnEqual` (MId :: MId (Cod f) (f a) (f a))
       \\ (proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a))

-- fmap (f . g) = fmap f . fmap g
law_MFunctor_assoc :: forall f m n a b c.
                     ( MFunctor f
                     , Cat m ~ Dom f, Cat n ~ Dom f
                     , Ok m a b, Ok n b c
                     ) => b `n` c -> a `m` b -> FnEqual (f a) (f c)
law_MFunctor_assoc g f = fmap (g .:. f) `fnEqual` (fmap g .:. fmap f)
                         \\ (proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a))
                         \\ (proveCod :: Obj (Dom f) b :- Obj (Cod f) (f b))
                         \\ (proveCod :: Obj (Dom f) c :- Obj (Cod f) (f c))



-- | Hask
class Hask a
instance Hask a

instance MCategory Hask

instance Morphism (->) where
    type Cat (->) = Hask
    chase = id

instance Discretization (->) where
    discretize = id

instance MFunctor [] where
    type Dom [] = Hask
    type Cod [] = Hask
    type Mor [] = (->)
    proveCod = Sub Dict
    fmap f [] = []
    fmap f (x:xs) = f `chase` x : fmap f xs

instance MFunctor ((->) a) where
    type Dom ((->) a) = Hask
    type Cod ((->) a) = Hask
    type Mor ((->) a) = (->)
    -- type Mor ((->) a) = MComp' Hask
    proveCod = Sub Dict
    fmap f g = chase f . chase g
    -- fmap f g = MComp' f g



-- | Num
instance MCategory Num

newtype (-.>) a b = NFun { getNFun :: a -> b }
    deriving (Generic, QC.Arbitrary, QC.CoArbitrary)
instance QC.Function (a -> b) => QC.Function (a -.> b)

instance Morphism (-.>) where
    type Cat (-.>) = Num
    chase = getNFun

instance Discretization (-.>) where
    discretize = NFun

newtype NList a = NList { getNList :: [a] }
    deriving (Eq, Ord, Read, Show, Generic, QC.Arbitrary, QC.CoArbitrary)

instance MFunctor NList where
    type Dom NList = Num
    type Cod NList = Hask
    type Mor NList = (->)
    proveCod = Sub Dict
    --- fmap f = discretize go
    ---     where go (NList []) = NList []
    ---           go (NList (x:xs)) = NList (f `chase` x :
    ---                                      getNList (fmap f (NList xs)))
    fmap f (NList xs) = NList (map (chase f) xs)

instance Num a => MFunctor ((-.>) a) where
    type Dom ((-.>) a) = Num
    type Cod ((-.>) a) = Hask
    type Mor ((-.>) a) = (->)
    proveCod = Sub Dict
    fmap f g = discretize (chase f . chase g)
