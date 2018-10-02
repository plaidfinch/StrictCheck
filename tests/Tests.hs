module Main where

import Specs
import RefTrans
import qualified Entangle

main :: IO ()
main = do
  -- specification unit tests
  runSpecs
  -- regression test for issue #2 (CSE breaks referential transparency)
  checkRefTrans
  Entangle.spec
