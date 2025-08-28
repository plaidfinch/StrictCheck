module Specs where

import Test.QuickCheck

import Test.StrictCheck
import Test.StrictCheck.Examples.Lists
import Test.StrictCheck.Examples.Map

import Control.Monad (when)
import GHC.IO.Encoding (textEncodingName)
import System.IO

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

  putStrLn "Checking bad_length_spec (failure is expected!)..."
  strictCheckSpecExact bad_length_spec (length :: [Int] -> Int)

  enc <- hGetEncoding stdout
  when (fmap textEncodingName enc == Just "UTF-8") $ do
    hSetEncoding stdout latin1
    putStrLn "Checking bad_length_spec without Unicode output (failure is expected!)..."
    strictCheckSpecExact bad_length_spec (length :: [Int] -> Int)
