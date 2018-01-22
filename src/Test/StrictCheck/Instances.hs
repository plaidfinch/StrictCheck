{-# language TypeOperators, TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.StrictCheck.Instances where

import Test.StrictCheck.Consume
import Test.StrictCheck.Produce
import Test.StrictCheck.Observe
import Test.QuickCheck

import Data.Tree
import Data.Map
import Data.Sequence

instance Consume ()
instance (Consume a, Consume b) => Consume (a, b)
instance (Consume a) => Consume [a]
instance (Consume a) => Consume (Tree a)

instance (Consume v) => Consume (Map k v) where
  consume = fields . fmap (consume . snd) . Data.Map.toList

instance Observe ()
instance (Observe a, Observe b) => Observe (a, b)
instance Observe a => Observe [a]
instance Observe a => Observe (Maybe a)
instance (Observe a, Observe b) => Observe (Either a b)

instance (Observe v) => Observe (Map k v) where
  type Demand (Map k v) = Map k `WithFieldsOf` v
  mapD     = mapWFO
  projectD = projectWFO
  embedD   = embedWFO

instance Observe a => Observe (Seq a) where
  type Demand (Seq a) = Seq `WithFieldsOf` a
  mapD = mapWFO
  projectD p m = WithFieldsOf (fmap p m)
  embedD e (WithFieldsOf m) = fmap e m

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
