{-# LANGUAGE TemplateHaskell, BangPatterns #-}

module Test.StrictCheck.Examples.Map where

import Prelude hiding (lookup)
import Debug.Trace

import qualified GHC.Generics as GHC
import Generics.SOP (Generic, HasDatatypeInfo, NS(..), hd, tl)

import Test.StrictCheck
import Test.StrictCheck.TH
import Test.StrictCheck.Observe
import Control.DeepSeq

import Data.Maybe
import Data.Function

import Test.QuickCheck
import Test.QuickCheck.Modifiers

import Control.Applicative

data Map k v = Bin (Map k v) k v (Map k v)
             | Empty
             deriving stock    (GHC.Generic, Show, Eq, Ord)
             deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

type KMap = Map (Int, Int) Int
  
$(derivePatternSynonyms ''Map)

replaceThunk :: (Shaped k, Shaped v) => Map k v -> Map k v -> Map k v
replaceThunk r m     | isThunk m = r
replaceThunk _ Empty             = Empty
replaceThunk r (Bin ml k v mr)   = Bin (replaceThunk r ml) k v (replaceThunk r mr)

fromList :: [((Int, Int), Int)] -> KMap
fromList = foldr (\(k, v) acc -> insert k v acc) Empty

insert :: (Ord k) => k -> v -> Map k v -> Map k v
insert key value Empty = Bin Empty key value Empty
insert key value (Bin ml k v mr) | key < k   = Bin (insert key value ml) k v mr
                                 | key > k   = Bin ml k v (insert key value mr)
                                 | otherwise = Bin ml key value mr

lookup :: KMap -> (Int, Int) -> Maybe Int
lookup Empty _                        = Nothing
lookup (Bin ml k' v mr) k | k == k'   = Just v
                          | k <  k'   = lookup ml k
                          | otherwise = lookup mr k

keys :: Map k v -> [k]
keys Empty           = []
keys (Bin ml k _ mr) = keys ml ++ [k] ++ keys mr

(!) :: KMap -> (Int, Int) -> Int
(!) m k = case lookup m k of
            Nothing -> 0 
            Just v  -> v

weights :: [Int]
weights = [10, 20, 30]

values :: [Int]
values = [60, 100, 120]

limit :: Int
limit = 50

solutionStep :: Map (Int, Int) Int -> Map (Int, Int) Int
solutionStep soln =
  fromList [((j, k), knapsack j k) | j <- [0 .. length weights-1], k <- [0 .. limit]]
  where
    knapsack j k = if j - 1 < 0 || k - weights !! j < 0
                   then if j >= 0 && weights !! j <= k then values !! j else 0
                   else max (soln ! (j-1, k))
                            (soln ! (j-1, k - weights !! j) + values !! j)

solution :: Map (Int, Int) Int
solution = fix solutionStep

pattern Pair' :: Demand a -> Demand b -> Demand (a, b)
pattern Pair' x y = Wrap (Eval (GS (Z (x :* y :* Nil))))

iterSolution :: (Int, Int) -> Int -> Map (Int, Int) Int -> Maybe Int
iterSolution k n soln = lookup m k
  where m | n <= 0    = soln
          | otherwise = (iterate solutionStep soln) !! n

iterSolutionWithKey :: Key -> Int -> Map (Int, Int) Int -> Maybe Int
iterSolutionWithKey (Key k) = iterSolution k

newtype Key = Key { getKey :: (Int, Int) }
  deriving stock    (GHC.Generic, Show, Eq, Ord)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

instance Arbitrary Key where
  -- Just to make sure keys are within the parameters of the problem
  arbitrary = fmap Key $
    (,) <$> elements [0 .. length weights - 1] <*> elements [0 .. limit]

instance Arbitrary KMap where
  -- I need to generate only valid pre-fixpoints, which is either
  -- Empty (iterated 0 times), or iterate once on Empty, or twice, and
  -- so on
  arbitrary = do
    NonNegative n <- arbitrary
    return $ (iterate solutionStep Empty) !! n

instance Produce KMap where
  -- I don't need lazy functions on KMaps. Since the spec only checks
  -- whether a particular entry in the KMap is evaluated or not.
  produce = arbitrary

instance Produce Key where
  -- I don't need lazy functions on keys either.
  produce = arbitrary

{-
strictCheckWithResults
  stdArgs{maxSize=100, maxSuccess=500}
  shrinkViaArbitrary
  genViaProduce
  strictnessViaSized
  iterSolution_spec
  iterSolutionWithKey
-}
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
