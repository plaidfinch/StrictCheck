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

testList2 :: [Integer]
testList2 = [7,8,9,10,11]

whnfContext :: a -> ()
whnfContext = flip seq ()

-- reverse should be spine strict on whnf
testReverse :: Test
testReverse =
  spineStrict testList ~=? dIn
  where (_ {-dOut-}, dIn) = observe1 whnfContext reverse testList

-- rotate (from Okasaki Queues) should be whnf strict on whnf
rotate :: [a] -> [a] -> [a] -> [a]
rotate []            []  as =                       as
rotate []       (b : bs) as =     rotate [] bs (b : as)
rotate (f : fs)      []  as = f : rotate fs []      as
rotate (f : fs) (b : bs) as = f : rotate fs bs (b : as)

testRotate :: Test
testRotate =
  whnf testList ~=? dIn
  where (_ {-dOut-}, dIn) = observe1 whnfContext (\fs -> rotate fs testList2 []) testList

tests :: Test
tests = TestList [
    TestLabel "Data.List reverse" testReverse
  , TestLabel "Data.List rotate"  testRotate
  ]

main :: IO ()
main = do
  result <- runTestTT tests
  putStrLn $ showCounts result
  if errors result + failures result > 0
    then exitFailure
    else exitSuccess
