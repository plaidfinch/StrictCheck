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
import Type.Reflection
import Control.Monad
import Data.List

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

instance Shaped Int where
  type Shape Int = Prim Int
  project    = projectPrim
  embed      = embedPrim
  match      = matchPrim
  render     = prettyPrim

instance Shaped Char where
  type Shape Char = Prim Char
  project    = projectPrim
  embed      = embedPrim
  match      = matchPrim
  render     = prettyPrim

instance Shaped Bool

instance (Typeable a, Typeable b) => Shaped (a -> b) where
  type Shape (a -> b) = Prim (a -> b)
  project = projectPrim
  embed = embedPrim
  match (Prim f) (Prim g) k = k (flatPrim f) (Just $ flatPrim g)
  render _ = prettyConstant ("<function> :: " ++ show (typeRep @(a -> b)))

-- instance (Typeable a, Typeable b) => Shaped (a -> b) where
--   type Demand (a -> b) = Opaque (a -> b)
--   projectD    = projectOpaque
--   embedD      = embedOpaque
--   withFconstructor 0D = withFconstructor 0Opaque
--   matchD      = matchOpaque
--   prettyD _   = prettyConstant "<function>"

-- instance (Shaped v, Typeable k, Ord k, Show k) => Shaped (Map k v) where
--   type Demand (Map k v) = Map k `Containing` v
--   projectD = projectContainer
--   embedD   = embedContainer
--   withFconstructor 0D =
--     withFconstructor 0Container $ \m k ->
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

instance Produce () where produce = arbitrary
instance Produce Int where produce = arbitrary
instance Produce Integer where produce = arbitrary

instance (Produce a, Produce b) => Produce (a, b) where
  produce =
    (,) <$> recur <*> recur

instance (Produce a) => Produce [a] where
  produce =
    frequency [ (1, return [])
              , (1, (:) <$> recur
                        <*> recur)
              ]

instance (Produce a) => Produce (Tree a) where
  produce =
    Node <$> recur
         <*> frequency [ (1, return [])
                       , (2, recur) ]
