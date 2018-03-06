{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-dodgy-exports -fno-warn-unused-imports #-}

module Test.StrictCheck
  ( module Curry
  , module Test.StrictCheck.Shaped
  , module Test.StrictCheck.Produce
  , module Test.StrictCheck.Consume
  , module Test.StrictCheck.Observe
  , module Test.StrictCheck.Instances
  , module Test.StrictCheck.Demands

  , NP(..), I(..)

  , strictCheckSpecExact
  , strictCheckWithResults
  , compareToSpecWith
  , equalToSpec
  , evaluationForall
  , shrinkEvalWith
  , Spec(..)
  , Evaluation(..)
  )
  where


import Test.StrictCheck.Curry as Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Instances
import Test.StrictCheck.Demands
import Test.StrictCheck.Shaped
import Test.StrictCheck.Shaped.Flattened

import Generics.SOP hiding (Shape)
import Generics.SOP.NP
import qualified GHC.Generics as GHC

import Test.QuickCheck hiding (Args, Result, function)
import qualified Test.QuickCheck as QC

import Data.List
import Control.DeepSeq
import Data.Functor.Product
import Data.Maybe
import Data.Coerce
import qualified Unsafe.Coerce as UNSAFE
import Data.IORef
import System.IO
import Control.Monad
import Type.Reflection

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

type family Map f args where
  Map f '[       ] = '[]
  Map f (a : args) = f a : Map f args

type Demands args = Map Demand args

newtype Spec args result =
  Spec (forall r. (args ⋯-> r)
        -> result
        -> args ⋯-> r)

getSpec
  :: forall r args result.
  Spec args result
  -> (args ⋯-> r)
  -> result
  -> args ⋯-> r
getSpec (Spec s) k d = s @r k d

curryCollect :: forall (xs :: [*]) r. Curry xs => (NP I xs -> r) -> xs ⋯-> r
curryCollect k = Curry.curry @xs k

compareToSpecWith
  :: forall args result.
  (SListI args, All Shaped args, Curry args, Curry (Demands args), Shaped result)
  => NP DemandComparison args
  -> Spec args result
  -> Evaluation args result
  -> Maybe (NP Demand args)
compareToSpecWith comparisons spec (Evaluation inputs inputsD resultD) =
  let prediction =
        Curry.uncurry
          (getSpec @(NP Demand args) spec collectDemands (fromDemand $ E resultD))
          inputs
      correct =
        all id . hcollapse $
          hcliftA3 (Proxy :: Proxy Shaped)
          (\(DemandComparison c) iD iD' -> K $ iD `c` iD')
            comparisons
            inputsD
            prediction
  in if correct then Nothing else Just prediction
  where
    collectDemands :: args ⋯-> NP Demand args
    collectDemands = curryCollect @args (hcmap (Proxy :: Proxy Shaped) (toDemand . unI))

equalToSpec
  :: forall args result.
  (SListI args, All Shaped args, Curry args, Curry (Demands args), Shaped result)
  => Spec args result
  -> Evaluation args result
  -> Maybe (NP Demand args)
equalToSpec spec e =
  compareToSpecWith compareEquality spec e

type Strictness = Int

type StrictCheck function =
  ( SListI (Args function)
  , Shaped (Result function)
  , Consume (Result function)
  , Curry (Args function)
  , Curry (Demands (Args function))
  , NFData (Shape (Result function) Demand)
  , All Typeable (Args function)
  , All Shaped (Args function)
  , All (Compose NFData Demand) (Args function))

strictCheckWithResults ::
  forall function evidence.
  StrictCheck function
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
          (evaluationForall @function gens strictness function)
          (shrinkEvalWith @function shrinks function) $
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
  :: forall function.
  ( StrictCheck function
  , All Arbitrary (Args function)
  , All Produce (Args function)
  ) => Spec (Args function) (Result function)
    -> function
    -> IO ()
strictCheckSpecExact spec function =
  do (maybeExample, result) <-
       strictCheckWithResults
         stdArgs
         shrinkViaArbitrary
         genViaProduce
         strictnessViaSized
         (equalToSpec spec)
         function
     -- print result
     (putStrLn . head . lines) (output result)
     case maybeExample of
       Nothing -> return ()
       Just example ->
         putStrLn (displayCounterSpec example)

displayCounterSpec
  :: forall args result.
  (Shaped result, All Shaped args, SListI args)
  => (Evaluation args result, NP Demand args) -> String
displayCounterSpec (Evaluation inputs inputsD resultD, predictedInputsD) =
  inputString
  ++ resultString
  ++ "\n" ++ replicate (80 `min` lineMax) '─' ++ "\n"
  ++ predictedDemandString
  ++ demandString
  where
    inputString =
      "\n Input" ++ plural ++ ":            "
      ++ showBulletedNPWith @Shaped (prettyDemand . interleave Eval . unI) inputs
    resultString =
      " Demand on result:    "
      ++ prettyDemand @result (E resultD)
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

instance (All Typeable args, Typeable result)
  => Show (Evaluation args result) where
  show _ =
    "<Evaluation"
    ++ " @[" ++ intercalate ", " argTypes ++ "]"
    ++ " @" ++ show (typeRep :: TypeRep result)
    ++ ">"
    where
      argTypes :: [String]
      argTypes =
        hcollapse
        $ hliftA (K . show)
        $ (hcpure (Proxy :: Proxy Typeable) typeRep :: NP TypeRep args)

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
  :: forall f.
  ( Curry (Args f)
  , Consume (Result f)
  , Shaped (Result f)
  , All Shaped (Args f)
  , NFData (Shape (Result f) Demand)
  , All (Compose NFData Demand) (Args f)
  ) => NP Gen (Args f)
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
    go :: Strictness
       -> (Result f -> Omega)
       -> NP I (Args f)
       -> Evaluation (Args f) (Result f)
    go s tO is =
      let (resultD, inputsD) =
            observeNP (forceOmega s . tO) (uncurryAll @f function) is
      in case resultD of
        T -> go (s + 1) tO is
        E posResultD ->
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
  :: forall f.
  ( Curry (Args f)
  , Shaped (Result f)
  , All Shaped (Args f)
  , All (Compose NFData Demand) (Args f)
  , NFData (Shape (Result f) Demand)
  ) => NP Shrink (Args f)
    -> f
    -> Evaluation (Args f) (Result f)
    -> [Evaluation (Args f) (Result f)]
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
             T     -> Nothing
             E pos -> Just pos

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
  let results = map (map (Prelude.uncurry f)) (grid x y)
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
