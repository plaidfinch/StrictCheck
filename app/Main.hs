{-# LANGUAGE FlexibleInstances, DeriveGeneric, UndecidableInstances #-}
import LazyCoArbitrary

import GHC.Generics
import Test.QuickCheck

data MyList a = MyNil | MyCons a (MyList a)
  deriving (Show, Generic)

class ArbitraryK1 a where
  arbitraryK1 :: Gen a -> Gen a

instance Arbitrary a => ArbitraryK1 [a] where
  arbitraryK1 g =
    -- No base case! 
    frequency [ (1, (:) <$> arbitrary <*> g ) ]

class ArbitraryK a where
  arbitraryK :: Gen a -> Gen a 

instance ArbitraryK1 a => ArbitraryK a where
  -- | TODO: Weights towards g?
  arbitraryK g = oneof [ g , arbitraryK1 (arbitraryK g) ]

class CoArbitraryK a where
  coarbitraryK :: ArbitraryK b => a -> Gen b -> Gen b

instance (CoArbitraryK a, CoArbitraryK b) => CoArbitraryK (a,b) where
  coarbitraryK t g = do
    arbitraryK $ frequency [ (1, variant 0 g)
                           , (1, let (x,y) = t in
                                 coarbitraryK x $ coarbitraryK y g ) ]

instance (CoArbitraryK a, ArbitraryK [a]) => CoArbitraryK [a] where
  coarbitraryK l g = do
    arbitraryK $ frequency [ (1, variant 0 g)
                           , (1, case l of
                                 [] -> variant 1 g
                                 x : xs -> variant 2 $ coarbitraryK (x,xs) g ) ]
      
-- | Annoying boilerplate line
instance LazyCoArbitrary a => LazyCoArbitrary (MyList a)

myListFromList :: [a] -> MyList a
myListFromList = foldr MyCons MyNil 

instance Arbitrary a => Arbitrary (MyList a) where
  arbitrary = myListFromList <$> arbitrary

testProp :: (LazyCoarb (MyList Int) -> Int) -> MyList Int -> Bool
testProp f l = (f . LazyCoarb) l == (f . LazyCoarb) l

-- | Temporary show function. Should we use "show functions"? 
instance Show (LazyCoarb (MyList Int) -> Int) where
  show f = "<function>"

main = do
  quickCheck testProp
