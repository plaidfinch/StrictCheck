module Main where

import Specs
import RefTrans

main :: IO ()
main = do
  -- specification unit tests
  runSpecs
  -- regression test for issue #2 (CSE breaks referential transparency)
  checkRefTrans
