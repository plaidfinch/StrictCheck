{-# LANGUAGE TemplateHaskell, BangPatterns #-}

{- | This module showcases another type of specification different from those in
   "Test.StrictCheck.Examples.List". Here, we demonstrate that StrictCheck is
   able to distinguish value-lazy maps from value-strict maps.

   In this module, we first develop the solution of the Knapsack dynamic
   programming problem by taking the fixpoint of a step function of the solution
   table. We represent the solution table with a map, and write a specification
   that is critical for the termination of this solution.
-}
module Test.StrictCheck.Examples.Map where

import Prelude hiding (lookup)
import Debug.Trace

import qualified GHC.Generics as GHC
import Generics.SOP (Generic, HasDatatypeInfo, NS(..), hd, tl)

import Test.StrictCheck
import Test.StrictCheck.TH

import Data.Maybe
import Data.Function

import Test.QuickCheck

-- | We roll our own map type to avoid dealing with abstract types.
data Map k v = Bin (Map k v) k v (Map k v) -- ^ A node that contains a key value pair
             | Empty                       -- ^ An empty node
             deriving stock    (GHC.Generic, Show, Eq, Ord)
             deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped)

-- | A specialized map useful for knapsack. The pair of ints represent the two
-- parameters to each knapsack sub-problem solved along the way. These two
-- parameters determine the subsequence of items each sub-problem is concerned
-- with, and the weight limit.
type KMap = Map (Int, Int) Int

$(derivePatternSynonyms ''Map)

-- | This replaces the thunk in a map partial value with the `r` parameter. This
-- is very similar to the `cap` function in the lists example.
replaceThunk :: (Shaped k, Shaped v) => Map k v -> Map k v -> Map k v
replaceThunk r m     | isThunk m = r
replaceThunk _ Empty             = Empty
replaceThunk r (Bin ml k v mr)   = Bin (replaceThunk r ml) k v (replaceThunk r mr)

-- | A helper for building a map from a list of values.
fromList :: [((Int, Int), Int)] -> KMap
fromList = foldr (\(k, v) acc -> insert k v acc) Empty

-- | A simplified insert that ignores rebalancing since rebalancing is not
-- important for the spec we will write.
insert :: (Ord k) => k -> v -> Map k v -> Map k v
insert key value Empty = Bin Empty key value Empty
insert key value (Bin ml k v mr) | key < k   = Bin (insert key value ml) k v mr
                                 | key > k   = Bin ml k v (insert key value mr)
                                 | otherwise = Bin ml key value mr

-- | The lookup function specialized for knapsack.
lookup :: KMap -> (Int, Int) -> Maybe Int
lookup Empty _                        = Nothing
lookup (Bin ml k' v mr) k | k == k'   = Just v
                          | k <  k'   = lookup ml k
                          | otherwise = lookup mr k

-- | This function extracts all of the keys of a map.
keys :: Map k v -> [k]
keys Empty           = []
keys (Bin ml k _ mr) = keys ml ++ [k] ++ keys mr

-- | A lookup function that returns the default value `0` for keys that are not
-- in the map. This saves us from doing repeated pattern matching when querying
-- the solution table.
(!) :: KMap -> (Int, Int) -> Int
(!) m k = case lookup m k of
            Nothing -> 0
            Just v  -> v

-- | Weight parameters to the knapsack problem.
weights :: [Int]
weights = [10, 20, 30]

-- | Value parameters to the knapsack problem, note that this must be the same
-- length as `weights`.
values :: [Int]
values = [60, 100, 120]

-- | The weight limit of the knapsack problem.
limit :: Int
limit = 50

-- | One step of the knapsack computation. This is a direct translation from the
-- recurrence relation of the knapsack problem.
solutionStep :: Map (Int, Int) Int -> Map (Int, Int) Int
solutionStep soln =
  fromList [((j, k), knapsack j k) | j <- [0 .. length weights-1], k <- [0 .. limit]]
  where
    knapsack j k = if j - 1 < 0 || k - weights !! j < 0
                   then if j >= 0 && weights !! j <= k then values !! j else 0
                   else max (soln ! (j-1, k))
                            (soln ! (j-1, k - weights !! j) + values !! j)

-- | The fixpoint of the recurrence relation, which is also the solution for the
-- knapsack problem.
solution :: Map (Int, Int) Int
solution = fix solutionStep

-- | A pattern synonym for extracting demands of each component from the demand
-- of a pair.
pattern Pair' :: Demand a -> Demand b -> Demand (a, b)
pattern Pair' x y = Wrap (Eval (GS (Z (x :* y :* Nil))))

-- | This function computes the nth pre-fixpoint of the knapsack solution, and
-- looks up the value at the specified cell from the pre-fixpoint.
iterSolution :: (Int, Int) -> Int -> Map (Int, Int) Int -> Maybe Int
iterSolution k n soln = lookup m k
  where m | n <= 0    = soln
          | otherwise = (iterate solutionStep soln) !! n

-- | This is the same as `iterSolution`, but uses a newtype wrapper for the
-- index into the map since we want to write a customized `Arbitrary` instance
-- for `Key`.
iterSolutionWithKey :: Key -> Int -> Map (Int, Int) Int -> Maybe Int
iterSolutionWithKey (Key k) = iterSolution k

-- | The newtype wrapper of index into the knapsack solution table.
newtype Key = Key { getKey :: (Int, Int) }
  deriving stock    (GHC.Generic, Show, Eq, Ord)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped)

-- | The customized generator for `Key` that only generates valid keys given the
-- problem parameters.
instance Arbitrary Key where
  -- Just to make sure keys are within the parameters of the problem
  arbitrary = fmap Key $
    (,) <$> elements [0 .. length weights - 1] <*> elements [0 .. limit]

-- | The customized generator for solution tables that only generates valid
-- pre-fixpoints.
instance Arbitrary KMap where
  -- I need to generate only valid pre-fixpoints, which is either
  -- Empty (iterated 0 times), or iterate once on Empty, or twice, and
  -- so on
  arbitrary = do
    NonNegative n <- arbitrary
    return $ (iterate solutionStep Empty) !! n

-- | A dummy produce instance for the solution table.
instance Produce KMap where
  -- I don't need lazy functions on KMaps. Since the spec only checks
  -- whether a particular entry in the KMap is evaluated or not.
  produce = arbitrary

-- | A dummy produce instance for the index into the solution table.
instance Produce Key where
  -- I don't need lazy functions on keys either.
  produce = arbitrary

-- | This IO action ties the spec together with everything built so far, and
-- runs the StrictCheck randomized testing framework.
runMapTest :: IO ()
runMapTest = strictCheckWithResults
               stdArgs{maxSize=100, maxSuccess=1000}
               shrinkViaArbitrary
               genViaProduce
               strictnessViaSized
               iterSolution_spec
               iterSolutionWithKey >>= print

-- | This is the specification that establishes a property important for the
-- termination of `solution`: given any pre-fixpoint of `pre-solution`, forcing
-- the value at pre-solution[i][j] should not induce a demand at the (i, j) cell
-- of the input that steps to pre-solution, since otherwise this would be an
-- infinite loop in the fixpoint.
-- The value-lazy `Map` defined in this module satisfies this property. However,
-- if we make this `Map` value-strict using BangPatterns, StrictCheck will
-- report a failure when `runMapTest` is executed.
iterSolution_spec :: Evaluation '[Key, Int, KMap] (Maybe Int) -> Maybe (Int, Int)
iterSolution_spec (Evaluation args demands dOut) =
  let I (Key evalK) = hd args
      I nIter       = hd (tl args)
      dInM          = hd (tl (tl demands))
      inM           = replaceThunk Empty (fromDemand @KMap dInM)
      evalV         = lookup inM evalK
  in  if (inM == Empty)   ||
         isBaseCase evalK ||
         nIter <= 0       ||
         isThunk evalV    ||
         isNothing evalV
      then Nothing
      else trace ("KeyD: " ++ show evalK) $
           trace ("InD: " ++ prettyDemand dInM) $
           trace ("OutD: " ++ prettyDemand @(Maybe Int) (E dOut)) $
           trace ("isT: " ++ (show . isThunk $ lookup inM evalK)) $
           Just evalK
  where isBaseCase (j, k) = j - 1 < 0 || k - weights !! j < 0
