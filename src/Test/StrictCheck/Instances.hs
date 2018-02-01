{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-unused-imports #-}

module Test.StrictCheck.Instances where

import Test.StrictCheck.Consume
import Test.StrictCheck.Produce
import Test.StrictCheck.Observe
import Test.QuickCheck

import Data.Tree
import Data.Map hiding ( toList, map )
import qualified Data.Map as Map
import Data.Set hiding ( toList, map )
import qualified Data.Set as Set
import Data.Foldable
import Data.Sequence
import Data.Typeable
import qualified GHC.Generics as GHC
import Generics.SOP
import Control.DeepSeq

-- | Convenience type for representing demands upon abstract structures with one
-- type recursively-demanded type parameter (i.e. (Map k) or Seq)

newtype Containing h a f =
  Container (h (f a))
  deriving (Eq, Ord, Show, GHC.Generic, NFData)

projectContaining :: (Functor h, Observe a)
  => (forall x. Observe x => x -> f x)
  -> h a -> Containing h a f

embedContaining :: (Functor h, Observe a)
  => (forall x. Observe x => f x -> x)
  -> Containing h a f -> h a

projectContaining p            x  = Container (fmap p x)
embedContaining   e (Container x) =            fmap e x
-- prettyContaining  n (Container x) = Constr n (Left (fmap unK (toList x)))

instance Consume ()
instance (Consume a, Consume b) => Consume (a, b)
instance (Consume a) => Consume [a]
instance (Consume a) => Consume (Tree a)

instance (Consume v) => Consume (Map k v) where
  consume = fields . fmap (consume . snd) . Map.toList

instance (Consume v) => Consume (Seq v) where
  consume = fields . map consume . toList

instance (Consume v) => Consume (Set v) where
  consume = fields . map consume . Set.toList

instance Observe ()
instance (Observe a, Observe b) => Observe (a, b)
instance Observe a => Observe [a]
instance Observe a => Observe (Maybe a)
instance (Observe a, Observe b) => Observe (Either a b)

-- instance (Observe v, Typeable k) => Observe (Map k v) where
--   type Demand (Map k v) = Map k `Containing` v
--   projectD = projectContaining
--   embedD   = embedContaining

-- instance Observe a => Observe (Seq a) where
--   type Demand (Seq a) = Seq `Containing` a
--   projectD = projectContaining
--   embedD   = embedContaining

-- instance (Ord a, Observe a) => Observe (Set a) where
--   type Demand (Set a) = [] `Containing` a
--   projectD p = projectContaining p . Set.toList
--   embedD   e = Set.fromList . embedContaining e

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
