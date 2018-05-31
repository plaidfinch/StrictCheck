{-| The top-level interface to the StrictCheck library for random strictness
    testing.

    __Quick Start:__

    Want to explore the strictness of functions before you write specifications?
    Go to "Test.StrictCheck.Observe" and look at the functions 'observe1' and
    'observe'.

    Want to check the strictness of a function against a specification of its
    strictness?

    1. Write a 'Spec' describing your expectation of the function's behavior.
       See "Test.StrictCheck.Demand" for more on working with demands, and
       "Test.StrictCheck.Examples.Lists" for examples of some specifications of
       functions on lists.
    2. Check your function using 'strictCheckSpecExact', like so:

    > strictCheckSpecExact spec function

    If your function passes testing, you'll get a success message just like in
    "Test.QuickCheck"; if a counterexample to your specification is found, you
    will see a pretty Unicode box diagram describing the mismatch.

    __Hint:__ StrictCheck, just like QuickCheck, doesn't work with polymorphic
    functions. If you get baffling type errors, first make sure that all your
    types are totally concrete.
-}
module Test.StrictCheck
  ( -- * Specifying demand behavior
    Spec(..)
  , getSpec
  -- * Checking specifications
  , StrictCheck
  , strictCheckSpecExact
  , strictCheckWithResults
  -- * Providing arguments for 'strictCheckWithResults'
  , genViaProduce
  , Shrink(..)
  , shrinkViaArbitrary
  , Strictness
  , strictnessViaSized
  -- * Representing individual evaluations of functions
  , Evaluation(..)
  , evaluationForall
  , shrinkEvalWith
  -- * Comparing demands
  , DemandComparison(..)
  , compareToSpecWith
  , equalToSpec
    -- * Re-exported n-ary products from "Generics.SOP"
  , NP(..), I(..), All
  -- * Re-exports of the rest of the library
  , module Test.StrictCheck.Demand
  , module Test.StrictCheck.Observe
  , module Test.StrictCheck.Produce
  , module Test.StrictCheck.Consume
  , module Test.StrictCheck.Shaped
  )
  where


-- TODO: IMPORTANT: Add short descriptions to Haddock module headers

import Test.StrictCheck.Curry as Curry
import Test.StrictCheck.Produce
import Test.StrictCheck.Consume
import Test.StrictCheck.Observe
import Test.StrictCheck.Demand
import Test.StrictCheck.Shaped

import Test.StrictCheck.Internal.Omega
import Test.StrictCheck.Internal.Shrink
         ( Shrink(..), axialShrinks, fairInterleave )

import Generics.SOP hiding (Shape)

import Test.QuickCheck as Exported hiding (Args, Result, function)
import qualified Test.QuickCheck as QC

import Data.List
import Data.Maybe
import Data.IORef
import Type.Reflection

-- | The default comparison of demands: exact equality
compareEquality :: All Shaped xs => NP DemandComparison xs
compareEquality = hcpure (Proxy @Shaped) (DemandComparison (==))

-- | The default way to generate inputs: via 'Produce'
genViaProduce :: All Produce xs => NP Gen xs
genViaProduce = hcpure (Proxy @Produce) (freely produce)

-- | The default way to shrink inputs: via 'shrink' (from "Test.QuickCheck"'s
-- 'Arbitrary' typeclass)
shrinkViaArbitrary :: All Arbitrary xs => NP Shrink xs
shrinkViaArbitrary = hcpure (Proxy @Arbitrary) (Shrink shrink)

-- | The default way to generate random strictnesses: uniformly choose between
-- 1 and the test configuration's @size@ parameter
strictnessViaSized :: Gen Strictness
strictnessViaSized =
  Strictness <$> (choose . (1,) =<< getSize)

-- | A newtype for wrapping a comparison on demands
--
-- This is useful when constructing an 'NP' n-ary product of such comparisons.
newtype DemandComparison a =
  DemandComparison (Demand a -> Demand a -> Bool)

-- | A demand specification for some function @f@ is itself a function which
-- manipulates demand values for some function's arguments and results
--
-- A @Spec@ for @f@ wraps a function which takes, in order:
--
-- * a continuation @predict@ which accepts all of @f@'s argument types in order,
-- * an implicit representation of a demand on @f@'s result (embedded in @f@'s
--   actual result type using special bottom values, see the documentation for
--   "Test.StrictCheck.Demand" for details), and
-- * all of @f@'s original arguments in order
--
-- The intention is that the @Spec@ will call @predict@ on some set of demands
-- representing the demands it predicts that @f@ will exert on its inputs,
-- given the provided demand on @f@'s outputs.
--
-- For example, here is a correct @Spec@ for 'take':
--
-- > take_spec :: Spec '[Int, [a]] [a]
-- > take_spec =
-- >  Spec $ \predict d n xs ->
-- >    predict n (if n > length xs then d else d ++ thunk)
--
-- See the documentation for "Test.StrictCheck.Demand" for information about how
-- to manipulate these implicit demand representations when writing @Spec@s, and
-- see the documentation for "Test.StrictCheck.Examples.Lists" for more examples
-- of writing specifications.
newtype Spec args result
  = Spec (forall r. (args ⋯-> r) -> result -> args ⋯-> r)

-- | Unwrap a @Spec@ constructor, returning the contained CPS-ed specification
--
-- Conceptually, this is the inverse to the @Spec@ constructor, but because
-- @Spec@ is variadic, @getSpec . Spec@ and @Spec . getSpec@ don't typecheck
-- without additional type annotation.
getSpec
  :: forall r args result.
  Spec args result
  -> (args ⋯-> r)
  -> result
  -> args ⋯-> r
getSpec (Spec s) k d = s @r k d

-- | Given a list of ways to compare demands, a demand specification, and an
-- evaluation of a particular function, determine if the function met the
-- specification, as decided by the comparisons. If so, return the prediction
-- of the specification.
compareToSpecWith
  :: forall args result.
  (All Shaped args, Curry args, Shaped result)
  => NP DemandComparison args
  -> Spec args result
  -> Evaluation args result
  -> Maybe (NP Demand args)
compareToSpecWith comparisons spec (Evaluation inputs inputsD resultD) =
  let prediction =
        Curry.uncurry
          (getSpec @(NP Demand args)
             spec
             collectDemands
             (fromDemand $ E resultD))
          inputs
      correct =
        all id . hcollapse $
          hcliftA3 (Proxy @Shaped)
          (\(DemandComparison c) iD iD' -> K $ iD `c` iD')
            comparisons
            inputsD
            prediction
  in if correct then Nothing else Just prediction
  where
    collectDemands :: args ⋯-> NP Demand args
    collectDemands =
      curryCollect @args (hcmap (Proxy @Shaped) (toDemand . unI))

curryCollect
  :: forall (xs :: [*]) r. Curry xs => (NP I xs -> r) -> xs ⋯-> r
curryCollect k = Curry.curry @xs k

-- | Checks if a given 'Evaluation' exactly matches the prediction of a given
-- 'Spec', returning the prediction of that @Spec@ if not
--
-- __Note:__ In the case of __success__ this returns @Nothing@; in the case of
-- __failure__ this returns @Just@ the incorrect prediction.
equalToSpec
  :: forall args result.
  (All Shaped args, Shaped result, Curry args)
  => Spec args result
  -> Evaluation args result
  -> Maybe (NP Demand args)
equalToSpec spec e =
  compareToSpecWith compareEquality spec e

-- | A @Strictness@ represents (roughly) how strict a randomly generated
-- function or evaluation context should be
--
-- An evaluation context generated with some strictness @s@ (i.e. through
-- 'evaluationForall') will consume at most @s@ constructors of its input,
-- although it might consume fewer.
newtype Strictness
  = Strictness Int
  deriving stock (Eq, Ord)
  deriving newtype (Show, Num)

-- | A function can be checked against a specification if it meets the
-- @StrictCheck@ constraint
type StrictCheck function =
  ( Shaped (Result function)
  , Consume (Result function)
  , Curry (Args function)
  , All Typeable (Args function)
  , All Shaped (Args function) )

-- | The most general function for random strictness testing: all of the more
-- convenient such functions can be derived from this one
--
-- Given some function @f@, this takes as arguments:
--
-- * A 'QC.Args' record describing arguments to pass to the underlying
--   QuickCheck engine
-- * An 'NP' n-ary product of 'Shrink' shrinkers, one for each argument of @f@
-- * An 'NP' n-ary product of 'Gen' generators, one for each argument of @f@
-- * A 'Gen' generator for strictnesses to be tested
-- * A predicate on 'Evaluation's: if the 'Evaluation' passes the predicate,
--   it should return @Nothing@; otherwise, it should return @Just@ some
--   @evidence@ representing the failure (when checking 'Spec's, this evidence
--   comes in the form of a @Spec@'s (incorrect) prediction)
-- * the function @f@ to be tested
--
-- If all tests succeed, @(Nothing, result)@ is returned, where @result@ is the
-- underlying 'QC.Result' type from "Test.QuickCheck". If there is a test
-- failure, it also returns @Just@ the failed 'Evaluation' as well as whatever
-- @evidence@ was produced by the predicate.
strictCheckWithResults ::
  forall function evidence.
  StrictCheck function
  => QC.Args
  -> NP Shrink (Args function)  -- TODO: allow dependent shrinking
  -> NP Gen (Args function)     -- TODO: allow dependent generation
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
      quickCheckWithResult qcArgs{chatty = False{-, maxSuccess = 10000-}} $
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

-- | Check a function to see whether it exactly meets a strictness specification
--
-- If the function fails to meet the specification, a counterexample is
-- pretty-printed in a box-drawn diagram illustrating how the specification
-- failed to match the real observed behavior of the function.
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
     (putStrLn . head . lines) (output result)
     case maybeExample of
       Nothing -> return ()
       Just example ->
         putStrLn (Prelude.uncurry displayCounterSpec example)

------------------------------------------------------------
-- An Evaluation is what we generate when StrictCheck-ing --
------------------------------------------------------------

-- | A snapshot of the observed strictness behavior of a function
--
-- An @Evaluation@ contains the 'inputs' at which a function was called, the
-- 'inputDemands' which were induced upon those inputs, and the 'resultDemand'
-- which induced that demand on the inputs.
data Evaluation args result =
  Evaluation
    { inputs       :: NP I      args    -- ^ Inputs to a function
    , inputDemands :: NP Demand args    -- ^ Demands on the input
    , resultDemand :: PosDemand result  -- ^ Demand on the result
    }

instance (All Typeable args, Typeable result)
  => Show (Evaluation args result) where
  show _ =
    "<Evaluation> :: Evaluation"
    ++ " '[" ++ intercalate ", " argTypes ++ "]"
    ++ " " ++ show (typeRep :: TypeRep result)
    where
      argTypes :: [String]
      argTypes =
        hcollapse
        $ hliftA (K . show)
        $ (hcpure (Proxy @Typeable) typeRep :: NP TypeRep args)


-----------------------------------
-- Generating random evaluations --
-----------------------------------

-- | Given a list of generators for a function's arguments and a generator for
-- random strictnesses (measured in number of constructors evaluated), create
-- a generator for random 'Evaluation's of that function in random contexts
evaluationForall
  :: forall f.
  ( Curry (Args f)
  , Consume (Result f)
  , Shaped (Result f)
  , All Shaped (Args f)
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
    go (Strictness s) tO is =
      let (resultD, inputsD) =
            observeNP (forceOmega s . tO) (uncurryAll @f function) is
      in case resultD of
        T -> go (Strictness s + 1) tO is
        E posResultD ->
          Evaluation is inputsD posResultD


---------------------------
-- Shrinking evaluations --
---------------------------

-- | Given a shrinker for each of the arguments of a function, the function
-- itself, and some 'Evaluation' of that function, produce a list of smaller
-- @Evaluation@s of that function
shrinkEvalWith
  :: forall f.
  ( Curry (Args f)
  , Shaped (Result f)
  , All Shaped (Args f)
  ) => NP Shrink (Args f)
    -> f
    -> Evaluation (Args f) (Result f)
    -> [Evaluation (Args f) (Result f)]
shrinkEvalWith
  shrinks (uncurryAll -> function) (Evaluation inputs _ resultD) =
    let shrunkDemands   = shrinkDemand @(Result f) resultD
        shrunkInputs    = fairInterleave (axialShrinks shrinks inputs)
        shrinkingDemand = mapMaybe      (reObserve inputs)  shrunkDemands
        shrinkingInputs = mapMaybe (flip reObserve resultD) shrunkInputs
    in fairInterleave [ shrinkingDemand, shrinkingInputs ]
  where
    reObserve
      :: NP I (Args f)
      -> PosDemand (Result f)
      -> Maybe (Evaluation (Args f) (Result f))
    reObserve is rD =
      let (rD', isD) = observeNP (evaluateDemand rD) function is
      in fmap (Evaluation is isD) $
           case rD' of
             T     -> Nothing
             E pos -> Just pos


-- | Render a counter-example to a specification (that is, an 'Evaluation'
-- paired with some expected input demands it doesn't match) as a Unicode
-- box-drawing sketch
displayCounterSpec
  :: forall args result.
  (Shaped result, All Shaped args)
  => Evaluation args result
  -> NP Demand args
  -> String
displayCounterSpec (Evaluation inputs inputsD resultD) predictedInputsD =
  beside inputBox ("   " : "───" : repeat "   ") resultBox
  ++ (flip replicate ' ' $
       (2 `max` (subtract 2 $ (lineMax [inputString] `div` 2))))
  ++ "🡓 🡓 🡓\n"
  ++ beside
       actualBox
       ("       " : "       " : "  ═╱═  " : repeat "       ")
       predictedBox
  where
    inputBox =
      box "┌" '─'         "┐"
          "│" inputHeader "├"
          "├" '─'         "┤"
          "│" inputString "│"
          "└" '─'         "┘"

    resultBox =
      box "┌" '─'          "┐"
          "┤" resultHeader "│"
          "├" '─'          "┤"
          "│" resultString "│"
          "└" '─'          "┘"

    actualBox =
      box "┌" '─'                "┐"
          "│" actualHeader       "│"
          "├" '─'                "┤"
          "│" actualDemandString "│"
          "└" '─'                "┘"

    predictedBox =
      box "┌" '─'                   "┐"
          "│" predictedHeader       "│"
          "├" '─'                   "┤"
          "│" predictedDemandString "│"
          "└" '─'                   "┘"

    inputHeader = " Input" ++ plural
    resultHeader = " Demand on result"
    actualHeader = " Actual input demand" ++ plural
    predictedHeader = " Spec's input demand" ++ plural

    inputString =
      showBulletedNPWith @Shaped (prettyDemand . interleave Eval . unI) inputs
    resultString = " " ++ prettyDemand @result (E resultD)
    actualDemandString =
      showBulletedNPWith @Shaped prettyDemand inputsD
    predictedDemandString =
      showBulletedNPWith @Shaped prettyDemand predictedInputsD

    rule w l c r = frame w l (replicate w c) r ++ "\n"

    frame w before str after =
      before ++ str
      ++ (replicate (w - length str) ' ')
      ++ after

    frames w before para after =
      unlines $ map (\str -> frame w before str after) (lines para)

    beside l cs r =
      unlines . take (length ls `max` length rs) $
        zipWith3
          (\x c y -> x ++ c ++ y)
          (ls ++ repeat (replicate (lineMax [l]) ' '))
          cs
          (rs ++ repeat "")
      where
        ls = lines l
        rs = lines r

    box top_l    top    top_r
        header_l header header_r
        div_l    div_c  div_r
        body_l   body   body_r
        bottom_l bottom bottom_r =
      let w = lineMax [header, body]
      in rule   w top_l    top    top_r
      ++ frames w header_l header header_r
      ++ rule   w div_l    div_c  div_r
      ++ frames w body_l   body   body_r
      ++ rule   w bottom_l bottom bottom_r

    lineMax strs =
      (maximum . map
        (\(lines -> ls) -> maximum (map length ls) + 1) $ strs)

    plural = case inputs of
      (_ :* Nil) -> ""
      _          -> "s"

    showBulletedNPWith
      :: forall c g xs. All c xs
      => (forall x. c x => g x -> String) -> NP g xs -> String
    -- showBulletedNPWith display (x :* Nil) = " " ++ display x ++ "\n"
    showBulletedNPWith display list = showNPWith' list
      where
        showNPWith' :: forall ys. All c ys => NP g ys -> String
        showNPWith'      Nil = ""
        showNPWith' (y :* ys) =
          " • " ++ display y ++ "\n" ++ showNPWith' ys
