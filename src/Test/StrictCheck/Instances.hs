
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.StrictCheck.Instances where

import Test.StrictCheck.Consume
import Test.StrictCheck.Produce
import Test.QuickCheck

import Data.Tree

instance (Consume a, Consume b) => Consume (a, b)
instance (Consume a) => Consume [a]
instance (Consume a) => Consume (Tree a)

instance Produce Integer where
  produce = produceArbitrary

instance Consume Integer where
  consume = consumeCoArbitrary

instance (Produce a, Produce b) => Produce (a, b) where
  produce inputs =
    (,) <$> recur inputs <*> recur inputs

instance (Produce a) => Produce [a] where
  produce inputs = do
    frequency [ (1, return [])
              , (1, (:) <$> recur inputs
                        <*> recur inputs)
              ]

instance (Produce a) => Produce (Tree a) where
  produce input =
    Node <$> recur input
         <*> frequency [ (1, return [])
                       , (2, recur input) ]
