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
import qualified Test.QuickCheck as QC

import Data.List
import Control.DeepSeq
import Data.Functor.Product
import Data.Maybe
import Data.Coerce
import Data.IORef
import System.IO
import Control.Monad


compareEquality :: All Shaped xs => NP DemandComparison xs
compareEquality = hcpure (Proxy :: Proxy Shaped) (DemandComparison eqDemand)

genViaProduce :: All Produce xs => NP Gen xs
genViaProduce = hcpure (Proxy :: Proxy Produce) (freely produce)

shrinkViaArbitrary :: All Arbitrary xs => NP Shrink xs
shrinkViaArbitrary = hcpure (Proxy :: Proxy Arbitrary) (Shrink shrink)

strictnessViaSized :: Gen Strictness
strictnessViaSized = choose . (1,) =<< getSize

newtype DemandComparison a =
  DemandComparison (Demand a -> Demand a -> Bool)

compareToSpec :: _ => (NP I args -> Demand result -> NP Demand args)
              -> NP DemandComparison args
              -> Evaluation args result
              -> Maybe (NP Demand args)
compareToSpec spec comparisons (Evaluation inputs inputsD resultD) =
  let prediction = spec inputs (Wrap (E resultD))
      correct =
        all id . hcollapse $
          hcliftA3 (Proxy :: Proxy Shaped)
          (\(DemandComparison c) iD iD' -> K $ iD `c` iD')
            comparisons
            inputsD
            prediction
  in if correct then Nothing else Just prediction

type Strictness = Int

strictCheckWithResults ::
  forall function evidence. _
  => QC.Args
  -> NP Shrink (Args function)
  -> NP Gen (Args function)
  -> Gen Strictness
  -> (Evaluation (Args function) (Result function) -> Maybe evidence)
  -> function
  -> IO ( Maybe ( Evaluation (Args function) (Result function)
                , evidence )
        , QC.Result )
strictCheckWithResults
  qcArgs shrinks gens strictness predicate function = do
    ref <- newIORef Nothing
    result <-
      quickCheckWithResult qcArgs{chatty = False} $
        forAllShrink
          (evaluationForall gens strictness function)
          (shrinkEvalWith shrinks function) $
            \example ->
              case predicate example of
                Nothing ->
                  property True
                Just evidence ->
                  whenFail (writeIORef ref $ Just (example, evidence)) False
    readIORef ref >>= \case
      Nothing      -> pure (Nothing,      result)
      Just example -> pure (Just example, result)

strictCheckSpecExact
  :: _
  => (NP I (Args function)
      -> Demand (Result function)
      -> NP Demand (Args function))
  -> function
  -> IO ()
strictCheckSpecExact spec function =
  do (maybeExample, result) <-
       strictCheckWithResults
         stdArgs
         shrinkViaArbitrary
          genViaProduce
          strictnessViaSized
          (compareToSpec spec compareEquality)
          function
     (putStrLn . head . lines) (output result)
     case maybeExample of
       Nothing -> return ()
       Just example ->
         putStrLn (displayCounterSpec example)

displayCounterSpec
  :: forall args result. _ => (Evaluation args result, NP Demand args) -> String
displayCounterSpec (Evaluation inputs inputsD resultD, predictedInputsD) =
  inputString
  ++ resultString
  ++ "\n" ++ replicate (80 `min` lineMax) '─' ++ "\n"
  ++ predictedDemandString
  ++ demandString
  where
    inputString =
      "\n Input" ++ plural ++ ":            "
      ++ showBulletedNPWith @Shaped (prettyDemand . interleave E . unI) inputs
    resultString =
      " Demand on result:    "
      ++ prettyDemand @result (Wrap (E resultD))
    demandString =
      " Demand on input" ++ plural ++ " (predicted):"
      ++ showBulletedNPWith @Shaped prettyDemand predictedInputsD
    predictedDemandString =
      " Demand on input" ++ plural ++ " (actual):   "
      ++ showBulletedNPWith @Shaped prettyDemand inputsD

    lineMax =
      maximum . map
      (\(lines -> ls) -> maximum (map length ls) + 1) $
      [inputString, resultString, demandString, predictedDemandString]

    plural = case inputs of
      (_ :* Nil) -> ""
      _          -> "s"


------------------------------------------------------------
-- An Evaluation is what we generate when StrictCheck-ing --
------------------------------------------------------------

data Evaluation args result =
  Evaluation (NP I      args)    -- ^ Inputs to a function
             (NP Demand args)    -- ^ Demands on the input
             (PosDemand result)  -- ^ Demand on the result

-- instance Show (Evaluation args result) where show _ = "<evaluation>"

instance (All Show args, All Shaped args, Shaped result)
  => Show (Evaluation args result) where
  show (Evaluation inputs inputsD resultD) =
    "\n Input" ++ plural ++ ":              " ++ inputString ++
    " Demand on result:   " ++ resultString ++
    "\n" ++ replicate (19 `max` (80 `min` lineMax)) '─' ++ "\n" ++
    " Demand on input" ++ plural ++ ":    " ++ demandString
    where
      inputString =
        showBulletedNPWith @Shaped (prettyDemand . interleave E . unI) inputs
      resultString =
        prettyDemand @result (Wrap (E resultD))
      demandString =
        showBulletedNPWith @Shaped prettyDemand inputsD

      lineMax =
        maximum . map
        (\(lines -> ls) -> (if length ls == 1 then 22 else 0)
                           + maximum (map length ls)) $
        [inputString, resultString, demandString]

      plural = case inputs of
        (_ :* Nil) -> ""
        _          -> "s"

-- TODO: For consistency, use prettyDemand to show inputs too

showBulletedNPWith :: forall c g xs. All c xs
                   => (forall x. c x => g x -> String) -> NP g xs -> String
showBulletedNPWith display (x :* Nil) = "   " ++ display x ++ "\n"
showBulletedNPWith display list = "\n" ++ showNPWith' list
  where
    showNPWith' :: forall ys. All c ys => NP g ys -> String
    showNPWith'      Nil = ""
    showNPWith' (y :* ys) =
      "   • " ++ display y ++ "\n" ++ showNPWith' ys

-- TODO: Do not export this constructor!


-----------------------------------
-- Generating random evaluations --
-----------------------------------

evaluationForall
  :: forall f. (Consume (Result f), _)
  => NP Gen (Args f)
  -> Gen Strictness
  -> f
  -> Gen (Evaluation (Args f) (Result f))
evaluationForall gens strictnessGen function = do
  inputs     <- hsequence gens
  strictness <- strictnessGen
  toOmega    <- freely produce
  return (go strictness toOmega inputs)
  where
    -- If context is fully lazy, increase strictness until it forces something
    go s tO is =
      let (resultD, inputsD) =
            observeNP (forceOmega s . tO) (uncurryAll function) is
      in case resultD of
        Wrap T -> go (s + 1) tO is
        Wrap (E posResultD) ->
          Evaluation is inputsD posResultD

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

-- TODO: make shrinking work instead over positive demands

shrinkEvalWith
  :: forall f. _
  => NP Shrink (Args f) -> f -> Evaluation (Args f) (Result f) -> [Evaluation (Args f) (Result f)]
shrinkEvalWith
  shrinks (uncurryAll -> function) (Evaluation inputs _ resultD) =
    let shrunkDemands = shrinkDemand @(Result f) resultD
        shrunkInputs  = fairInterleave (axialShrinks shrinks inputs)
        shrinkingDemand = mapMaybe      (reObserve inputs)  shrunkDemands
        shrinkingInputs = mapMaybe (flip reObserve resultD) shrunkInputs
    in fairInterleave [ shrinkingDemand, shrinkingInputs ]
  where
    reObserve :: NP I (Args f) -> PosDemand (Result f) -> Maybe (Evaluation (Args f) (Result f))
    reObserve is rD =
      let (rD', isD) = observeNP (evaluate rD) function is
      in fmap (Evaluation is isD) $
           case rD' of
             Wrap T       -> Nothing
             Wrap (E pos) -> Just pos

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
