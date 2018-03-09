{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -ddump-splices #-}

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
import Test.StrictCheck.TH
import Test.StrictCheck.Shaped.Flattened

import Generics.SOP
import Generics.SOP.NP

import Control.DeepSeq
import System.Exit
import qualified GHC.Generics as GHC

import Data.List

import qualified Test.StrictCheck.Examples.Lists as EL
import Knapsack
import Specs

-- Tests on lists
testList :: [Integer]
testList = [1,2,3,4,5,6]

testList2 :: [Integer]
testList2 = [7,8,9,10,11]

whnfContext :: a -> ()
whnfContext = flip seq ()

-- Evaluates the first n cells
spineStrictUpToContext :: Int -> [a] -> ()
spineStrictUpToContext n = spineStrictContext . take n

spineStrictContext :: [a] -> ()
spineStrictContext = flip seq () . foldl' (flip (:)) []

-- reverse should be spine strict on whnf
testReverse :: Test
testReverse =
  spineStrict testList ~=? dIn
  where (_ {-dOut-}, dIn) = observe1 whnfContext reverse testList

-- summing the list will be fully strict
testFoldrSum :: Test
testFoldrSum =
  nf testList ~=? dIn
  where (_ {-dOut-}, dIn) = observe1 whnfContext (foldr (+) 0) testList

-- append should be spineStrict in the first list, whnf on the second list
testAppend :: Test
testAppend =
  TestList [
    spineStrict testList  ~=? dIn1
  , whnf        testList2 ~=? dIn2
  ]
  where (_ {-dOut-}, dIns) = observe
                               (spineStrictUpToContext $ length testList + 1)
                               (++) testList testList2

        dIn1 = hd dIns
        dIn2 = hd (tl dIns)
  
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

-- Trees
data BinTree a = Leaf
               | Node (BinTree a) a (BinTree a)
               deriving stock    (GHC.Generic, Show, Eq, Ord)
               deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

$(derivePatternSynonyms ''BinTree)

testTree1 :: BinTree Integer
testTree1 = Node Leaf 1 Leaf

testTree2 :: BinTree Integer
testTree2 = Node Leaf 3 Leaf

testTree3 :: BinTree Integer
testTree3 = Node testTree1 2 testTree2

reverseTree :: BinTree a -> BinTree a
reverseTree Leaf                  = Leaf
reverseTree (Node tleft d tright) = Node (reverseTree tright) d (reverseTree tleft)

-- reverse tree is lazy
testReverseTree :: Test
testReverseTree =
  whnf testTree3 ~=? dIn
  where (_ {-dOut-}, dIn) = observe1 whnfContext reverseTree testTree3

data WeirdPair a b = LeftPair a
                   | RightPair a b
                   | Integer :** b
               deriving stock    (GHC.Generic, Show, Eq, Ord)
               deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

$(derivePatternSynonyms ''WeirdPair)

-- Some tests on using pattern synonyms
testWP1 :: WeirdPair Integer ()
testWP1 = LeftPair 1

testWP2 :: WeirdPair Integer ()
testWP2 = RightPair 1 ()

testWP3 :: WeirdPair () ()
testWP3 = 1 :** ()

testPatSyn :: Test
testPatSyn = TestList [
    TestCase $ (LeftPair' (Wrap Thunk))           @=? (whnf testWP1)
  , TestCase $ (RightPair' (Wrap Thunk) (Wrap Thunk)) @=? (whnf testWP2)
  , TestCase $ ((Wrap Thunk) :**% (Wrap Thunk))       @=? (whnf testWP3)
  ]

-- The main test suite containing all the tests
testSuite :: Test
testSuite = TestList [
    TestLabel "Data.List reverse"     testReverse
  , TestLabel "Data.List rotate"      testRotate
  , TestLabel "Data.List foldr (+)"   testFoldrSum
  , TestLabel "Data.List (++)"        testAppend
  , TestLabel "BinTree   reverseTree" testReverseTree
  , TestLabel "PatternSynonyms"       testPatSyn
  ]

main :: IO ()
main = do

  -- Hook for testing that the rotate rewrite is correct
  strictCheckSpecExact EL.rot_simple_spec (EL.rot' @Int)
  
--  putStrLn "rotate spec"
--  strictCheckSpecExact EL.rot_spec (EL.rot @Int)
--  putStrLn "reverse + append (should fail)"
--  strictCheckSpecExact EL.rot_spec (EL.rot' @Int)
--  putStrLn "rewritten spec on rotate"
--  strictCheckSpecExact EL.rot_spec' (EL.rot @Int)
--  putStrLn "rewritten spec on rev ++ append (should fail)"
--  strictCheckSpecExact EL.rot_spec' (EL.rot' @Int)
-- 
--  -- Original test suite
--  result <- runTestTT testSuite
--  putStrLn $ showCounts result
--  if errors result + failures result > 0
--    then exitFailure
--    else exitSuccess

  putStrLn "Running example specs:"
  runSpecs

  putStrLn "Running unit tests:"
  result <- runTestTT testSuite
  putStrLn $ showCounts result
  if errors result + failures result > 0
    then exitFailure
    else exitSuccess
