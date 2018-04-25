{-# LANGUAGE UndecidableInstances #-}

module Applicative
    ( Applicative(..)
    , law_Applicative_id
    , law_Applicative_comp
    , law_Applicative_homo
    , law_Applicative_inter
    , law_Applicative_id'
    , law_Applicative_id_left'
    , law_Applicative_id_right'
    , law_Applicative_assoc'
    , (<$>)
    , ZipList(..)
    ) where

import Prelude hiding ( id, (.), curry, uncurry
                      , Functor(..)
                      , Applicative(..), (<$>)
                      )

import Control.Applicative (ZipList(..))
import Data.Constraint
import Data.Functor.Compose as F
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product as F
import Data.List.NonEmpty hiding (repeat)
import Data.Proxy
import Data.Semigroup

import Category
import Functor



-- | Applicative
class Functor f => Applicative f where
    {-# MINIMAL pure, ((<*>), liftA2' | liftA2) #-}
    pure :: Obj (Dom f) a => a -> f a
    infixl 4 <*>
    (<*>) :: (Obj (Dom f) a, Obj (Dom f) b)
             => f (Dom f a b) -> Cod f (f a) (f b)
    default (<*>) :: forall a b.
                     ( Obj (Dom f) a, Obj (Dom f) b
                     , Closed (Dom f), Closed (Cod f)
                     , Cod f ~ (->)
                     ) => f (Dom f a b) -> Cod f (f a) (f b)
    (<*>) = liftA2 id
            \\ (proveClosed ::
                    (Obj (Dom f) a, Obj (Dom f) b) :- Obj (Dom f) (Dom f a b))
    liftA2 :: ( Closed (Dom f), Closed (Cod f)
              , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
              ) => Dom f a (Dom f b c) -> Cod f (f a) (Cod f (f b) (f c))
    default liftA2 :: forall a b c.
                      ( Closed (Dom f) --, Closed (Cod f)
                      , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
                      , Cod f ~ (->)
                      ) => Dom f a (Dom f b c) ->
                           Cod f (f a) (Cod f (f b) (f c))
    liftA2 f x y = f <$> x <*> y
                   \\ (proveClosed ::
                           (Obj (Dom f) b, Obj (Dom f) c) :-
                           Obj (Dom f) (Dom f b c))
    liftA2' :: ( Cartesian (Dom f), Cartesian (Cod f)
               , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
               ) => Dom f (Prod (Dom f) a b) c ->
                    Cod f (Prod (Cod f) (f a) (f b)) (f c)
    default liftA2' :: forall a b c.
                       ( Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
                       , Closed (Dom f), Closed (Cod f)
                       ) => Dom f (Prod (Dom f) a b) c ->
                            Cod f (Prod (Cod f) (f a) (f b)) (f c)
    liftA2' f = uncurry (liftA2 (curry f))
                \\ (proveCod :: Obj (Dom f) a :- Obj (Cod f) (f a))
                \\ (proveCod :: Obj (Dom f) b :- Obj (Cod f) (f b))
                \\ (proveCod :: Obj (Dom f) c :- Obj (Cod f) (f c))

-- identity: pure id <*> v = v
law_Applicative_id :: (Applicative f, Cod f ~ (->)
                      , Obj (Dom f) a, Obj (Dom f) (Dom f a a)
                      ) => f a -> Equal (f a)
law_Applicative_id xs = (pure id <*> xs) `equal` xs

-- composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
law_Applicative_comp :: (Applicative f, Dom f ~ Cod f, Cod f ~ (->)
                        , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
                        ) => f (Dom f b c) -> f (Dom f a b) -> f a ->
                             Equal (f c)
law_Applicative_comp gs fs xs =
    (pure (.) <*> gs <*> fs <*> xs) `equal` (gs <*> (fs <*> xs))

-- homomorphism: pure f <*> pure x = pure (f x)
law_Applicative_homo :: (Applicative f, Dom f ~ Cod f, Cod f ~ (->))
                        => Proxy f -> Dom f a b -> a -> Equal (f b)
law_Applicative_homo _ f x = (pure f <*> pure x) `equal` pure (f x)

-- interchange: u <*> pure y = pure ($ y) <*> u
law_Applicative_inter :: (Applicative f, Dom f ~ Cod f, Cod f ~ (->))
                         => f (Dom f a b) -> a -> Equal (f b)
law_Applicative_inter fs x = (fs <*> pure x) `equal` (pure ($ x) <*> fs)

-- f :: a -> b
-- x :: a
-- liftA2' (\((), x) -> f x) (pure (), xs) = fmap f xs
law_Applicative_id' :: forall f a b k p u l q.
                       ( Applicative f
                       , Cartesian (Dom f), Cartesian (Cod f)
                       , Obj (Dom f) a, Obj (Dom f) b
                       , Cod f ~ (->)
                       , k ~ Dom f, p ~ Prod k, u ~ Unit p
                       , l ~ Cod f, q ~ Prod l
                       ) => a `k` b -> f a -> Equal (f b)
law_Applicative_id' f xs =
    liftA2' f' xs' `equal` fmap f xs
    where
      f' :: p u a `k` b
      f' = unapply (\p -> let (_, x) = unprod p in f `apply` x)
           \\ (proveCartesian @k :: (Obj k u, Obj k a) :- Obj k (p u a))
      xs' :: q (f u) (f a)
      xs' = prod (pure (punit @p), xs)

-- f :: (a, b) -> c
-- x :: a
-- ys :: f b
-- liftA2' f (pure x, ys) = fmap (\x -> f (x, y)) ys
law_Applicative_id_left' ::
    forall f a b c k p.
       ( Applicative f, Cartesian (Dom f), Cartesian (Cod f)
       , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
       , Cod f ~ (->)
       , k ~ Dom f, p ~ Prod k
       ) => p a b `k` c -> a -> f b -> Equal (f c)
law_Applicative_id_left' f x ys =
    liftA2' f (prod (pure x, ys)) `equal`
    fmap (unapply (\y -> f `apply` prod (x, y))) ys
       \\ (proveCartesian @k :: (Obj k a, Obj k b) :- Obj k (p a b))

-- liftA2' f (xs, pure y) = fmap (\y -> f (x, y)) xs
-- f :: (a, b) -> c
-- xs :: f a
-- y :: b
law_Applicative_id_right' ::
    forall f a b c k p.
       ( Applicative f, Cartesian (Dom f), Cartesian (Cod f)
       , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c
       , Cod f ~ (->)
       , k ~ Dom f, p ~ Prod k
       ) => p a b `k` c -> f a -> b -> Equal (f c)
law_Applicative_id_right' f xs y =
    liftA2' f (prod (xs, pure y)) `equal`
    fmap (unapply (\x -> f `apply` prod (x, y))) xs
       \\ (proveCartesian @k :: (Obj k a, Obj k b) :- Obj k (p a b))

-- f :: a -> a'
-- g :: b -> b'
-- h :: c -> c'
-- i :: (a', (b', c')) -> d
-- liftA2' hi (liftA2' fg (xs, ys), zs) = liftA2' fi (xs, liftA2' gh (ys, zs))
law_Applicative_assoc' ::
    forall f a a' b b' c c' d k p.
       ( Applicative f, Cartesian (Dom f), Cartesian (Cod f)
       , Obj (Dom f) a, Obj (Dom f) b, Obj (Dom f) c, Obj (Dom f) d
       , Obj (Dom f) a', Obj (Dom f) b', Obj (Dom f) c'
       , Cod f ~ (->)
       , k ~ Dom f, p ~ Prod k
       ) => a `k` a' -> b `k` b' -> c `k` c' -> (p a' (p b' c')) `k` d ->
            f a -> f b -> f c -> Equal (f d)
law_Applicative_assoc' f g h i xs ys zs =
    liftA2' hi (liftA2' fg (xs, ys), zs) `equal`
    liftA2' fi (xs, liftA2' gh (ys, zs))
       \\ (proveCartesian @k :: (Obj k a', Obj k b') :- Obj k (p a' b'))
       \\ (proveCartesian @k :: (Obj k b', Obj k c') :- Obj k (p b' c'))
    where fg :: p a b `k` p a' b'
          fg = unapply (\p -> let (x, y) = unprod p
                              in prod (f `apply` x, g `apply` y))
               \\ (proveCartesian @k :: (Obj k a, Obj k b) :- Obj k (p a b))
               \\ (proveCartesian @k :: (Obj k a', Obj k b') :- Obj k (p a' b'))
          hi :: p (p a' b') c `k` d
          hi = unapply (\p -> let (q', z) = unprod p
                                  (x', y') = unprod q'
                                  r' = prod (x', prod (y', h `apply` z))
                              in i `apply` r')
               \\ (proveCartesian @k ::
                       (Obj k (p a' b'), Obj k c) :- Obj k (p (p a' b') c))
               \\ (proveCartesian @k :: (Obj k a', Obj k b') :- Obj k (p a' b'))
               \\ (proveCartesian @k ::
                       (Obj k a', Obj k (p b' c')) :- Obj k (p a' (p b' c')))
               \\ (proveCartesian @k :: (Obj k b', Obj k c') :- Obj k (p b' c'))
          gh :: p b c `k` p b' c'
          gh = unapply (\p -> let (y, z) = unprod p
                              in prod (g `apply` y, h `apply` z))
               \\ (proveCartesian @k :: (Obj k b, Obj k c) :- Obj k (p b c))
               \\ (proveCartesian @k :: (Obj k b', Obj k c') :- Obj k (p b' c'))
          fi :: p a (p b' c') `k` d
          fi = unapply (\p -> let (x, q') = unprod p
                                  (y', z') = unprod q'
                                  r' = prod (f `apply` x, prod (y', z'))
                              in i `apply` r')
               \\ (proveCartesian @k ::
                       (Obj k a, Obj k (p b' c')) :- Obj k (p a (p b' c')))
               \\ (proveCartesian @k ::
                       (Obj k a', Obj k (p b' c')) :- Obj k (p a' (p b' c')))
               \\ (proveCartesian @k :: (Obj k b', Obj k c') :- Obj k (p b' c'))



infixl 4 <$>
(<$>) :: (Functor f, Obj (Dom f) a, Obj (Dom f) b)
         => Dom f a b -> Cod f (f a) (f b)
(<$>) = fmap



instance Applicative Proxy where
    pure _ = Proxy
    liftA2 _ Proxy Proxy = Proxy

instance Applicative Identity where
    pure = Identity
    liftA2 f (Identity x) (Identity y) = Identity (f x y)

instance Applicative (Either a) where
    pure = Right
    liftA2 _ (Left a) _ = Left a       -- keep first exception
    liftA2 _ (Right _) (Left b) = Left b
    liftA2 f (Right x) (Right y) = Right (f x y)

instance (Semigroup a, Monoid a) => Applicative ((,) a) where
    pure x = (mempty, x)
    liftA2 f (a, x) (b, y) = (a <> b, f x y)

instance Applicative ((->) a) where
    pure = const
    liftA2 f fx fy x = f (fx x) (fy x)

instance ( Applicative f, Applicative g, Functor (F.Product f g)
         , Dom f ~ Dom g, Cod f ~ Cod g, Cod f ~ (->)
         ) => Applicative (F.Product f g) where
    pure x = Pair (pure x) (pure x)
    Pair fs1 fs2 <*> Pair xs1 xs2 = Pair (fs1 <*> xs1) (fs2 <*> xs2)
    liftA2 f (Pair xs1 xs2) (Pair ys1 ys2) =
        Pair (liftA2 f xs1 ys1) (liftA2 f xs2 ys2)
    liftA2' f p =
        let (Pair xs1 xs2, Pair ys1 ys2) = unprod p
        in Pair (liftA2' f (prod (xs1, ys1))) (liftA2' f (prod (xs2, ys2)))

instance ( Applicative f, Applicative g, Functor (F.Compose f g)
         , Dom f ~ Cod g, Cod f ~ (->), Cod g ~ (->)
         ) => Applicative (F.Compose f g) where
    pure x = Compose (pure (pure x))
    Compose f <*> Compose x = Compose ((<*>) <$> f <*> x)
    liftA2 f (Compose xss) (Compose yss) = Compose (liftA2 (liftA2 f) xss yss)
    liftA2' f p =
        let (Compose xss, Compose yss) = unprod p
        in Compose (liftA2' (liftA2' f) (prod (xss, yss)))

instance (Semigroup a, Monoid a) => Applicative (Const a) where
    pure _ = Const mempty
    liftA2 _ (Const a) (Const b) = Const (a <> b)

instance Applicative Maybe where
    pure = Just
    liftA2 f (Just x) (Just y) = Just (f x y)
    liftA2 _ _ _ = Nothing

instance Applicative [] where
    pure x = [x]
    liftA2 f xs ys = [f x y | x <- xs, y <- ys]

instance Applicative NonEmpty where
    pure x = x :| []
    liftA2 f (x :| xs) (y :| ys) =
        case liftA2 f (x : xs) (y : ys) of
          [] -> undefined       -- this cannot happen
          r : rs -> r :| rs

instance Applicative ZipList where
    pure x = ZipList (repeat x)
    liftA2 f (ZipList (x:xs)) (ZipList (y:ys)) =
        let ZipList rs = liftA2 f (ZipList xs) (ZipList ys)
        in ZipList (f x y : rs)
    liftA2 _ _ _ = ZipList []
    -- liftA2 f (ZipList xs) (ZipList ys) = ZipList (zipWith f xs ys)

instance Applicative NList where
    pure x = NList [x]
    (<*>) = undefined
    liftA2' f (NList xs, NList ys) =
        NList [f `apply` NProd x y | x <- xs, y <- ys]
