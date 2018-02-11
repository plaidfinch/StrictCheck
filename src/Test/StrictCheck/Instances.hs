{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-unused-imports #-}

module Test.StrictCheck.Instances where

import Test.StrictCheck.Consume
import Test.StrictCheck.Produce
import Test.StrictCheck.Shaped
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

instance Shaped ()
instance (Shaped a, Shaped b) => Shaped (a, b)
instance Shaped a => Shaped [a]
instance Shaped a => Shaped (Maybe a)
instance (Shaped a, Shaped b) => Shaped (Either a b)

-- -- TODO: Custom prettyD for tuples

instance Shaped Integer where
  type Shape Integer = Prim Integer
  project    = projectPrim
  embed      = embedPrim
  match      = matchPrim
  render     = prettyPrim

-- instance (Typeable a, Typeable b) => Shaped (a -> b) where
--   type Demand (a -> b) = Opaque (a -> b)
--   projectD    = projectOpaque
--   embedD      = embedOpaque
--   withFieldsD = withFieldsOpaque
--   matchD      = matchOpaque
--   prettyD _   = prettyConstant "<function>"

-- instance (Shaped v, Typeable k, Ord k, Show k) => Shaped (Map k v) where
--   type Demand (Map k v) = Map k `Containing` v
--   projectD = projectContainer
--   embedD   = embedContainer
--   withFieldsD =
--     withFieldsContainer $ \m k ->
--       k (Map.elems m) (Map.fromList . zip (keys m))
--   matchD =
--     matchContainer $ \f m n ->
--       Map.fromList <$>
--         zipWithM (\(kM, vM) (kN, vN) ->
--                     if kM == kN
--                     then Just (kM, f vM vN)
--                     else Nothing)
--                  (assocs m)
--                  (assocs n)
--   prettyD (Container m) =
--     CustomD 10 $
--       [ Left (Right ("Data.Map", "fromList"))
--       , Left (Left " [")
--       ] ++
--       ( concat @[]
--       . intersperse [Left (Left ", ")]
--       . fmap prettyKeyVal
--       $ assocs (fmap unK m)
--       ) ++
--       [ Left (Left "]")
--       ]
--     where
--       prettyKeyVal (k, x) =
--         [ Left (Left $ "(" ++ show k ++ ", ")
--         , Right (0, x)
--         , Left (Left ")")
--         ]

-- instance Shaped a => Shaped (Seq a) where
--   type Demand (Seq a) = Seq `Containing` a
--   projectD = projectContaining
--   embedD   = embedContaining

-- instance (Ord a, Shaped a) => Shaped (Set a) where
--   type Demand (Set a) = [] `Containing` a
--   projectD p = projectContaining p . Set.toList
--   embedD   e = Set.fromList . embedContaining e

instance Produce () where
  produce = producePrimitive

instance Produce Integer where
  produce = producePrimitive

instance Consume Integer where
  consume = consumePrimitive

instance (Produce a, Produce b) => Produce (a, b) where
  produce input =
    (,) <$> recur input <*> recur input

instance (Produce a) => Produce [a] where
  produce input =
    frequency [ (1, return [])
              , (1, (:) <$> recur input
                        <*> recur input)
              ]

instance (Produce a) => Produce (Tree a) where
  produce input =
    Node <$> recur input
         <*> frequency [ (1, return [])
                       , (2, recur input) ]
