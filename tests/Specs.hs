module Specs where

import Test.QuickCheck
import Test.HUnit

import Test.StrictCheck
import Test.StrictCheck.Examples.Lists
import Test.StrictCheck.Examples.Map

import Data.Bifunctor (bimap)

runSpecs :: IO ()
runSpecs = do
  putStrLn "Checking length_spec..."
  strictCheckSpecExact length_spec (length :: [Int] -> Int)

  putStrLn "Checking take_spec..."
  strictCheckSpecExact take_spec (take :: Int -> [Int] -> [Int])

  putStrLn "Checking map_spec..."
  strictCheckSpecExact map_spec (map :: (Int -> [Int]) -> [Int] -> [[Int]])

  putStrLn "Checking rot_spec..."
  strictCheckSpecExact rot_spec (rot :: [Int] -> [Int] -> [Int])

  putStrLn "Checking append_spec..."
  strictCheckSpecExact append_spec ((++) :: [Int] -> [Int] -> [Int])

  putStrLn "Checking reverse_spec..."
  strictCheckSpecExact reverse_spec (reverse :: [Int] -> [Int])

  putStrLn "Checking knapsack..."
  strictCheckWithResults
    stdArgs{maxSize=100, maxSuccess=500}
    shrinkViaArbitrary
    genViaProduce
    strictnessViaSized
    iterSolution_spec
    iterSolutionWithKey >>= print

  putStrLn "Checking entangleShape"
  _ <- runTestTT . test $ do
    (x , d ) <- fmap (fmap prettyDemand) <$> entangleShape ()
    (x', d') <- fmap (fmap prettyDemand) <$> entangleShape x
    d1 <- d
    d1 @=? "_"
    d'1 <- d'
    d'1 @=? "_"
    d2 <- d
    d2 @=? "_"
    let !_ = x
    d3 <- d
    d3 @=? "()"
    d'2 <- d'
    d'2 @=? "_"
    let !_ = x'
    d'3 <- d'
    d'3 @=? "()"

  putStrLn "Checking observe"
  _ <- runTestTT . test $ do
    let strict = bimap prettyDemand prettyDemand (observe1 id (\() -> ()) ())
    let lazy   = bimap prettyDemand prettyDemand (observe1 id (\_  -> ()) ())

    strict @=? ("()", "()")
    lazy   @=? ("()", "_")

  return ()
