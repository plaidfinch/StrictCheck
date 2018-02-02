{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.StrictCheck.Instances where

import Test.StrictCheck.Consume
import Test.StrictCheck.Produce
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances.Tools
import Test.QuickCheck

import Data.Tree
import Data.Map hiding ( toList, map )
import qualified Data.Map as Map
import Data.Set hiding ( toList, map )
import qualified Data.Set as Set
import Data.Foldable
import Data.Sequence (Seq)
import Generics.SOP
import Data.Typeable
import Control.Monad
import Data.List

instance Generic (Tree a)

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

-- TODO: Custom prettyD for tuples

instance Observe Integer where
  type Demand Integer = Prim Integer
  projectD    = projectPrim
  embedD      = embedPrim
  withFieldsD = withFieldsPrim
  matchD      = matchPrim
  prettyD     = prettyPrim

instance (Observe v, Typeable k, Ord k, Show k) => Observe (Map k v) where
  type Demand (Map k v) = Map k `Containing` v
  projectD = projectContainer
  embedD   = embedContainer
  withFieldsD =
    withFieldsContainer $ \m k ->
      k (Map.elems m) (Map.fromList . zip (keys m))
  matchD =
    matchContainer $ \f m n ->
      Map.fromList <$>
        zipWithM (\(kM, vM) (kN, vN) ->
                    if kM == kN
                    then Just (kM, f vM vN)
                    else Nothing)
                 (assocs m)
                 (assocs n)
  prettyD (Container m) =
    CustomD 10 $
      [ Left (Right ("Data.Map", "fromList"))
      , Left (Left " [")
      ] ++
      ( concat @[]
      . intersperse [Left (Left ", ")]
      . fmap prettyKeyVal
      $ assocs (fmap unK m)
      ) ++
      [ Left (Left "]")
      ]
    where
      prettyKeyVal (k, x) =
        [ Left (Left $ "(" ++ show k ++ ", ")
        , Right (0, x)
        , Left (Left ")")
        ]

-- instance Observe a => Observe (Seq a) where
--   type Demand (Seq a) = Seq `Containing` a
--   projectD = projectContaining
--   embedD   = embedContaining

-- instance (Ord a, Observe a) => Observe (Set a) where
--   type Demand (Set a) = [] `Containing` a
--   projectD p = projectContaining p . Set.toList
--   embedD   e = Set.fromList . embedContaining e

instance Produce Integer where
  produce = producePrimitive

instance Consume Integer where
  consume = consumePrimitive

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
