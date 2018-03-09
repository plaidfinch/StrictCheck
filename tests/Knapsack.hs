{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -ddump-splices #-}

module Knapsack where

import qualified GHC.Generics as GHC

import Test.StrictCheck
import Test.StrictCheck.Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances
import Test.StrictCheck.Demands
import Test.StrictCheck.Shaped
import Test.StrictCheck.TH
import Test.StrictCheck.Shaped.Flattened
import Test.StrictCheck.Instances.Tools

import Control.DeepSeq

import Generics.SOP
import Generics.SOP.NP

import Data.Function

data LMap k v = Bin (LMap k v) k v (LMap k v)
              | Empty
              deriving stock    (GHC.Generic, Show, Eq, Ord)
              deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

$(derivePatternSynonyms ''LMap)

lFromList :: Ord k => [(k, v)] -> LMap k v
lFromList = foldr (\(k, v) acc -> insert k v acc) Empty

insert :: (Ord k) => k -> v -> LMap k v -> LMap k v
insert key value Empty = Bin Empty key value Empty
insert key value (Bin ml k v mr) | key < k   = Bin (insert key value ml) k v mr
                                 | key > k   = Bin ml k v (insert key value mr)
                                 | otherwise = Bin ml key value mr

(!) :: (Ord k) => LMap k v -> k -> v
(!) Empty k                        = error "Can't find this key"
(!) (Bin ml k' v mr) k | k == k'   = v
                       | k <  k'   = ml ! k
                       | otherwise = mr ! k

weights :: [Int]
weights = [10, 20, 30]

values :: [Int]
values = [60, 100, 120]

limit :: Int
limit = 50

solutionStep :: LMap (Int, Int) Int -> LMap (Int, Int) Int
solutionStep soln =
  lFromList [((j, k), knapsack j k) | j <- [0 .. length weights-1], k <- [0 .. limit]]
  where
    knapsack j k = if j - 1 < 0 || k - weights !! j < 0
                   then if weights !! j <= k then values !! j else 0
                   else max (soln ! (j-1, k))
                            (soln ! (j-1, k - weights !! j) + values !! j)

solution :: LMap (Int, Int) Int
solution = fix solutionStep

pattern Pair' :: Demand a -> Demand b -> Demand (a, b)
pattern Pair' x y = Wrap (Eval (GS (Z (x :* y :* Nil))))

lookupD :: Demand (LMap (Int, Int) Int) -> (Int, Int) -> Demand Int
lookupD Empty'                        _   = Wrap Thunk
lookupD (Bin' _  (Wrap Thunk)  _  _ ) _   = Wrap Thunk
lookupD (Bin' dL (Pair' dJ dK) dv dR) key =
  case (dJ, dK) of
    (Wrap (Eval dJ'), Wrap (Eval dK'))
      -> let key' = (unPrim dJ', unPrim dK')
         in if key == key'
            then dv
            else if key < key'
                 then lookupD dL key
                 else lookupD dR key
    _ -> error "Impossible"

iterSolution :: Int -> LMap (Int, Int) Int -> LMap (Int, Int) Int
iterSolution n soln = (iterate solutionStep soln) !! n
