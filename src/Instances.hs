
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Instances where

import FixGen
import Test.QuickCheck

import Continuations

-- Some instances!

instance Produce Integer where
  produce = produceAtomic

instance Consume Integer where
  consume = consumeAtomic

instance (Produce a, Produce b) => Produce (a, b) where
  produce field =
    (,) <$> field <*> field

instance (Consume a, Consume b) => Consume (a, b) where
  consume (x, y) =
    fields [ (1, consume x)
           , (1, consume y) ]

instance Produce Nat where
  produce field = do
    frequency [ (1, return Z)
              , (2, S <$> field)
              ]

instance Consume Nat where
  consume Z     = fields []
  consume (S n) = fields [ (1, consume n) ]

instance (Produce a) => Produce [a] where
  produce field = do
    frequency [ (1, return [])
              , (4, (:) <$> field
                        <*> field)
              ]

instance (Consume a) => Consume [a] where
  consume []       = fields []
  consume (x : xs) = fields [ (1, consume x)
                            , (1, consume xs)
                            ]
