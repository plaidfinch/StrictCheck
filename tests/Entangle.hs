module Entangle where

import Test.HUnit
import Test.StrictCheck
import Data.Bifunctor (bimap)

spec :: IO ()
spec = do
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

  pure ()
