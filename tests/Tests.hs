module Main where

import Test.HUnit

import Test.StrictCheck
import Test.StrictCheck.Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances
import Test.StrictCheck.Demands
import Test.StrictCheck.Shaped
import Test.StrictCheck.Shaped.Flattened

import System.Exit

import Data.List

-- Tests on lists
testList :: [Integer]
testList = [1,2,3,4,5,6]

whnfContext :: a -> ()
whnfContext = flip seq ()

-- reverse should be spine strict on whnf
testReverse :: Test
testReverse =
  spineStrict testList ~=? dIn
  where (_ {-dOut-}, dIn) = observe1 whnfContext reverse testList

tests :: Test
tests = TestList [
    TestLabel "Data.List reverse" testReverse
  ]

main :: IO ()
main = do
  result <- runTestTT tests
  putStrLn $ showCounts result
  if errors result + failures result > 0
    then exitFailure
    else exitSuccess
