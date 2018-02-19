{-# language PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_GHC -fno-warn-dodgy-exports -fno-warn-unused-imports #-}

module Test.StrictCheck
  -- ( module Test.StrictCheck.Curry
  -- , module Test.StrictCheck.Produce
  -- , module Test.StrictCheck.Consume
  -- , module Test.StrictCheck.Observe
  -- , module Test.StrictCheck.Instances
  -- , module Test.StrictCheck.Demands

  -- , module Generics.SOP
  -- , module Generics.SOP.NP
  -- )
  where


import Test.StrictCheck.Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances
import Test.StrictCheck.Demands
import Test.StrictCheck.Shaped
import Test.StrictCheck.Shaped.Flattened

import Generics.SOP
import Generics.SOP.NP
import qualified GHC.Generics as GHC

import Test.QuickCheck hiding (Args, Result, function)
import Data.List

import Test.StrictCheck.Internal.Inputs
import Control.DeepSeq
import Data.Functor.Product
import Data.Maybe
import Data.Coerce


data Options xs =
  Options { comparisons :: NP DemandComparison xs
          , generators  :: NP Gen xs
          , shrinks     :: NP Shrink xs
          }

defaultOptions :: (All Shaped xs, All Produce xs, All Arbitrary xs, SListI xs)
        => Options xs
defaultOptions =
  Options { comparisons = compareEquality
          , generators  = genViaProduce
          , shrinks     = shrinkViaArbitrary
          }

compareEquality :: All Shaped xs => NP DemandComparison xs
compareEquality = hcpure (Proxy :: Proxy Shaped) (DemandComparison eqDemand)

genViaProduce :: All Produce xs => NP Gen xs
genViaProduce = hcpure (Proxy :: Proxy Produce) (freely produce)

shrinkViaArbitrary :: All Arbitrary xs => NP Shrink xs
shrinkViaArbitrary = hcpure (Proxy :: Proxy Arbitrary) (Shrink shrink)

newtype DemandComparison a =
  DemandComparison (Demand a -> Demand a -> Bool)

compareToSpec
  :: forall function. _
  => Options (Args function)
  -> function
  -> (Demand (Result function)
      -> NP I (Args function)
      -> NP Demand (Args function))
  -> Property
compareToSpec
  Options{comparisons, generators, shrinks} function spec =
    forAllShrink
      (evaluationForall generators function)
      (shrinkEvaluationWith shrinks function) $
      \(Evaluation inputs inputsD resultD) ->
          all id . hcollapse $
            hcliftA3 (Proxy :: Proxy Shaped)
              (\(DemandComparison c) iD iD' -> K $ iD `c` iD')
              comparisons
              inputsD
              (spec resultD inputs)

------------------------------------------------------------
-- An Evaluation is what we generate when StrictCheck-ing --
------------------------------------------------------------

data Evaluation f =
  Evaluation (NP I      (Args   f))  -- ^ Inputs to a function
             (NP Demand (Args   f))  -- ^ Demands on the input
             (   Demand (Result f))  -- ^ Demand on the result

instance (All Show (Args f), All Shaped (Args f), Shaped (Result f))
  => Show (Evaluation f) where
  show (Evaluation inputs inputsD resultD) =
    "\nInput" ++ plural ++ ": " ++
    showBulletedNPWith @Show (show . unI) inputs ++
    "Demand on result: " ++ prettyDemand resultD ++
    "\n────────────────────────────────────────\n" ++
    "Demand on input" ++ plural ++ ": " ++
    showBulletedNPWith @Shaped prettyDemand inputsD
    where
      plural = case inputs of
        (_ :* Nil) -> ""
        _          -> "s"

showBulletedNPWith :: forall c g xs. All c xs
            => (forall x. c x => g x -> String) -> NP g xs -> String
showBulletedNPWith display (x :* Nil) = display x ++ "\n"
showBulletedNPWith display list = "\n" ++ showNPWith' list
  where
    showNPWith' :: forall ys. All c ys => NP g ys -> String
    showNPWith'      Nil = ""
    showNPWith' (y :* ys) =
      "  • " ++ display y ++ "\n" ++ showNPWith' ys

-- TODO: Do not export this constructor!


-----------------------------------
-- Generating random evaluations --
-----------------------------------

evaluationForall
  :: forall f. (Consume (Result f), _)
  => NP Gen (Args f) -> f -> Gen (Evaluation f)
evaluationForall inputGens (uncurryAll -> function) = do
  strictness <- choose . (1,) =<< getSize
  context <- (forceOmega strictness .) <$> freely produce
  inputs  <- hsequence inputGens
  let (resultD, inputsD) = observeNP context function inputs
  return $ Evaluation inputs inputsD resultD

evaluation
  :: forall f. (All Produce (Args f), Consume (Result f), _)
  => f -> Gen (Evaluation f)
evaluation =
  evaluationForall (hcpure (Proxy :: Proxy Produce) (freely produce))

data Omega = Succ Omega
  deriving (GHC.Generic, Generic, HasDatatypeInfo, Shaped)

instance Produce Omega where
  produce = Succ <$> recur

forceOmega :: Int -> Omega -> ()
forceOmega 0 _        = ()
forceOmega n (Succ o) = forceOmega (n - 1) o


---------------------------
-- Shrinking evaluations --
---------------------------

newtype Shrink a = Shrink (a -> [a])

shrinkEvaluationWith
  :: forall f. _ => NP Shrink (Args f) -> f -> Evaluation f -> [Evaluation f]
shrinkEvaluationWith
  shrinks (uncurryAll -> function) (Evaluation inputs _ resultD) =
    let shrunkDemands = shrinkDemand resultD
        shrunkInputs  = fairInterleave (axialShrinks shrinks inputs)
        shrinkingDemand = map      (reObserve inputs)  shrunkDemands
        shrinkingInputs = map (flip reObserve resultD) shrunkInputs
    in fairInterleave [ shrinkingDemand, shrinkingInputs ]
  where
    reObserve :: NP I (Args f) -> Demand (Result f) -> Evaluation f
    reObserve is rD =
      let (rD', isD) = observeNP (evaluate rD) function is
      in Evaluation is isD rD'

shrinkEvaluation :: forall f. _ => f -> Evaluation f -> [Evaluation f]
shrinkEvaluation =
  shrinkEvaluationWith (hcpure (Proxy :: Proxy Arbitrary) (Shrink shrink))

-- Fair n-ary axial shrinking (a.k.a. *fair* generalization of shrink on tuples)

data DZipper f whole where
  DZipper :: (NP f (c : rs) -> NP f whole)
          -> f c
          -> NP f rs
          -> DZipper f whole

next :: DZipper f whole -> Maybe (DZipper f whole)
next (DZipper _  _       Nil)  = Nothing
next (DZipper ls c (r :* rs')) =
  Just $ DZipper (ls . (c :*)) r rs'

positions :: NP f xs -> [DZipper f xs]
positions (dzipper -> mstart) =
  maybe [] go mstart
  where
    go start = start : maybe [] go (next start)

dzipper :: NP f xs -> Maybe (DZipper f xs)
dzipper       Nil = Nothing
dzipper (c :* rs) = Just $ DZipper id c rs

dzip :: DZipper f xs -> NP f xs
dzip (DZipper ls c rs) = ls (c :* rs)

centerIter :: (forall a. f a -> [f a]) -> DZipper f xs -> [DZipper f xs]
centerIter iter (DZipper ls c rs) =
  map (\c' -> DZipper ls c' rs) (iter c)

axialShrinks :: SListI xs => NP Shrink xs -> NP I xs -> [[NP I xs]]
axialShrinks shrinks xs =
  fmap (hliftA (\(Pair _ v) -> v) . dzip)
  . centerIter iter <$> positions withShrinks
  where
    iter (Pair (Shrink s) (I v)) = Pair (Shrink s) . I <$> (s v)
    withShrinks = hliftA2 Pair shrinks xs

fairInterleave :: [[a]] -> [a]
fairInterleave = roundRobin id
  where
    roundRobin k ((x : xs) : xss) = x : roundRobin (k . (xs :)) xss
    roundRobin k ([      ] : xss) = roundRobin k xss
    roundRobin k [              ] =
      case k [] of
        [ ] -> []
        xss -> roundRobin id xss

-- TODO: Think hard about what particular things to export from Generics.SOP
-- and, indeed, our own modules. And which modules to export other modules from

-- TODO: Get rid of these functions once we hit production...

-- TODO: Major documentation triage!

grid :: Integer -> Integer -> [[(Integer, Integer)]]
grid x y = map (\f -> map f [0..y]) $ map (,) [0..x]

withGrid :: Integer -> Integer -> IO (Integer -> Integer -> Integer)
withGrid x y = do
  f <- generate (freely produce)
  let results = map (map (uncurry f)) (grid x y)
  putStrLn ""
  mapM_ print results
  putStrLn ""
  mapM_ print (transpose results)
  return f

data Binary =
  N Binary Binary | L
  deriving stock (Eq, Ord, Show, GHC.Generic)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped)

binary :: Int -> Binary
binary 0 = L
binary n = N (binary (n - 1)) (binary (n - 1))


data D = C ()
  deriving stock (GHC.Generic, Show)
  deriving anyclass (Generic, HasDatatypeInfo, Consume, Shaped, NFData)

treeToOmega :: IO (Binary -> Omega)
treeToOmega = generate (freely produce)

forceBinaryN :: Int -> Binary -> ()
forceBinaryN _ L = ()
forceBinaryN 0 _ = ()
forceBinaryN n (N l r) =
  forceBinaryN (pred n) l `seq` forceBinaryN (pred n) r

observeTreeToOmega :: (Binary -> Omega) -> Int -> Int -> Demand Binary
observeTreeToOmega f m n = snd $ observe1 (forceOmega n) f (binary m)

-- TODO: "Evaluation" triple: inputs, result demand, input demands
-- Give it generation, shrinking, ...
