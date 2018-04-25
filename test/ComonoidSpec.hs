module ComonoidSpec where

import Prelude hiding (id, (.), curry, uncurry)

import Data.Monoid hiding ((<>))
import Data.Proxy
import Data.Semigroup
import Test.QuickCheck

import Category
import Comonoid



newtype A = A (Sum Integer)
    deriving ( Eq, Ord, Read, Show, Monoid, Num, Semigroup
             , Arbitrary
             , Cosemigroup, Comonoid
             )
newtype B = B (Sum Integer)
    deriving ( Eq, Ord, Read, Show, Monoid, Num, Semigroup
             , Arbitrary
             , Cosemigroup, Comonoid
             )



prop_A_Cosemigroup_inv :: A -> Property
prop_A_Cosemigroup_inv x = uncurry (===) (getEqual (law_Cosemigroup_inv x))

prop_A_Comonoid_counit :: A -> Property
prop_A_Comonoid_counit x = uncurry (===) (getEqual (law_Comonoid_counit x))

prop_A_Comonoid_inv :: A -> Property
prop_A_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



prop_B_Cosemigroup_inv :: B -> Property
prop_B_Cosemigroup_inv x = uncurry (===) (getEqual (law_Cosemigroup_inv x))

prop_B_Comonoid_counit :: B -> Property
prop_B_Comonoid_counit x = uncurry (===) (getEqual (law_Comonoid_counit x))

prop_B_Comonoid_inv :: B -> Property
prop_B_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



prop_Proxy_Cosemigroup_inv :: Proxy A -> Property
prop_Proxy_Cosemigroup_inv x = uncurry (===) (getEqual (law_Cosemigroup_inv x))

prop_Proxy_Comonoid_counit :: Proxy A -> Property
prop_Proxy_Comonoid_counit x = uncurry (===) (getEqual (law_Comonoid_counit x))

prop_Proxy_Comonoid_inv :: Proxy A -> Property
prop_Proxy_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



-- Either is not a Monoid. (Then why is it a Semigroup?)
-- prop_Either_Cosemigroup_inv :: Either A B -> Property
-- prop_Either_Cosemigroup_inv x =
--     uncurry (===) (getEqual (law_Cosemigroup_inv x))
-- 
-- prop_Either_Comonoid_counit :: Either A B -> Property
-- prop_Either_Comonoid_counit x =
--     uncurry (===) (getEqual (law_Comonoid_counit x))
-- 
-- prop_Either_Comonoid_inv :: Either A B -> Property
-- prop_Either_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



prop_Tuple_Cosemigroup_inv :: (A, B) -> Property
prop_Tuple_Cosemigroup_inv x = uncurry (===) (getEqual (law_Cosemigroup_inv x))

prop_Tuple_Comonoid_counit :: (A, B) -> Property
prop_Tuple_Comonoid_counit x = uncurry (===) (getEqual (law_Comonoid_counit x))

prop_Tuple_Comonoid_inv :: (A, B) -> Property
prop_Tuple_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



prop_Maybe_Cosemigroup_inv :: Maybe A -> Property
prop_Maybe_Cosemigroup_inv x = uncurry (===) (getEqual (law_Cosemigroup_inv x))

prop_Maybe_Comonoid_counit :: Maybe A -> Property
prop_Maybe_Comonoid_counit x = uncurry (===) (getEqual (law_Comonoid_counit x))

prop_Maybe_Comonoid_inv :: Maybe A -> Property
prop_Maybe_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



prop_List_Cosemigroup_inv :: [A] -> Property
prop_List_Cosemigroup_inv x = uncurry (===) (getEqual (law_Cosemigroup_inv x))

prop_List_Comonoid_counit :: [A] -> Property
prop_List_Comonoid_counit x = uncurry (===) (getEqual (law_Comonoid_counit x))

prop_List_Comonoid_inv :: [A] -> Property
prop_List_Comonoid_inv x = uncurry (===) (getEqual (law_Comonoid_inv x))



--TODO prop_Counter_Cosemigroup :: NonNegative Int -> Property
--TODO prop_Counter_Cosemigroup (NonNegative n) =
--TODO     take n (mapUnfold getCounter (Counter 0)) === [0 .. n - 1]
--TODO 
--TODO prop_CountDown_Cosemigroup :: NonNegative Int -> Property
--TODO prop_CountDown_Cosemigroup (NonNegative n) =
--TODO     mapUnfold getCountDown (CountDown n) === [n, n - 1 .. 1]
--TODO 
--TODO prop_Counted_Cosemigroup :: NonNegative Int -> A -> Property
--TODO prop_Counted_Cosemigroup (NonNegative n) x =
--TODO     unfold (Counted n x) ===
--TODO            take n (mapUnfold (Counted 1 . getForever) (Forever x))
--TODO 
--TODO prop_Forever_Cosemigroup :: NonNegative Int -> A -> Property
--TODO prop_Forever_Cosemigroup (NonNegative n) x =
--TODO     P.length (take n (unfold (Forever x))) === n
