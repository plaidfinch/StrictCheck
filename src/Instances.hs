
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Instances where

import Generate
import Test.QuickCheck

import Data.Tree

instance Produce Integer where
  produce = produceArbitrary

instance Consume Integer where
  consume = consumeWHNF

instance (Produce a, Produce b) => Produce (a, b) where
  produce inputs =
    (,) <$> recur inputs <*> recur inputs

instance (Consume a, Consume b) => Consume (a, b) where
  consume (x, y) =
    fields [ (1, consume x)
           , (1, consume y) ]

instance (Produce a) => Produce [a] where
  produce inputs = do
    frequency [ (1, return [])
              , (1, (:) <$> recur inputs
                        <*> recur inputs)
              ]

instance (Consume a) => Consume [a] where
  consume []       = fields []
  consume (x : xs) = fields [ (1, consume x)
                            , (1, consume xs)
                            ]

instance (Consume a) => Consume (Tree a) where
  consume (Node r cs) = fields [ (1, consume r)
                               , (1, consume cs) ]

instance (Produce a) => Produce (Tree a) where
  produce input =
    Node <$> recur input
         <*> frequency [ (1, return [])
                       , (2, recur input) ]
