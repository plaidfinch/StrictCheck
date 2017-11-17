{-# LANGUAGE FlexibleInstances, DeriveGeneric #-}
import LazyCoArbitrary

import GHC.Generics
import Test.QuickCheck

data MyList a = MyNil | MyCons a (MyList a)
  deriving (Show, Generic)

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

main =
  quickCheck testProp
