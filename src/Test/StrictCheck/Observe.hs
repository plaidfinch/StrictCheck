{-# language PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
module Test.StrictCheck.Observe where

import Control.DeepSeq
import Data.Bifunctor
import Control.Applicative
import Control.Monad.Identity
import Data.Functor.Product
import Data.Monoid ( Endo(..) )

import Prelude
import Data.IORef
import System.IO.Unsafe
import Control.Exception as Exception

import qualified GHC.Generics as GHC
import Generics.SOP hiding (Shape)

import Test.StrictCheck.Curry hiding (curry, uncurry)
import Test.StrictCheck.Shaped
import Test.StrictCheck.Shaped.Flattened


--------------------------------------------------------
-- The basic types which make up a demand description --
--------------------------------------------------------

-- TODO: rename Thunk constructors to allow patsyns to use these names

data Thunk a = Eval !a | Thunk
  deriving (Eq, Ord, Show, Functor, GHC.Generic, NFData)

instance Applicative Thunk where
  pure = Eval
  Thunk  <*> _      = Thunk
  _      <*> Thunk  = Thunk
  Eval f <*> Eval a = Eval (f a)

instance Num a => Num (Thunk a) where
  (+)         = liftA2 (+)
  (-)         = liftA2 (-)
  (*)         = liftA2 (*)
  abs         = fmap abs
  signum      = fmap signum
  fromInteger = Eval . fromInteger

type Demand = (%) Thunk

type PosDemand a = Shape a Demand

{-# COMPLETE E, T #-}

pattern E :: Shape a Demand -> Demand a
pattern E a = Wrap (Eval a)

pattern T :: Demand a
pattern T = Wrap Thunk

-- TODO: Do not export Unevaluated's constructor
data Unevaluated = Unevaluated deriving Show
instance Exception Unevaluated

toDemand :: Shaped a => a -> Demand a
toDemand = interleave toThunk
  where
    toThunk :: a -> Thunk a
    toThunk a = unsafePerformIO $
      (Eval <$> Exception.evaluate a)
      `catch`
      (\(_ :: Unevaluated) -> return Thunk)

fromDemand :: Shaped a => Demand a -> a
fromDemand = fuse fromThunk
  where
    fromThunk :: Thunk a -> a
    fromThunk (Eval a) = a
    fromThunk Thunk    = throw Unevaluated


------------------------------------------------------
-- Observing demand behavior of arbitrary functions --
------------------------------------------------------

-- | Force a value in some applicative context. This is useful for ensuring that
-- values are evaluated in the correct order inside of unsafePerformIO blocks.
eval :: Applicative f => a -> f ()
eval !_ = pure ()

{-# NOINLINE entangle #-}
entangle :: forall a. a -> (a, Thunk a)
entangle a =
  unsafePerformIO $ do
    ref <- newIORef Thunk
    return ( unsafePerformIO $ do
               writeIORef ref (Eval a)
               return a
           , unsafePerformIO $ readIORef ref )

{-# NOINLINE entangleShape #-}
entangleShape :: Shaped a => a -> (a, Demand a)
entangleShape =
  first (fuse unI)
  . (\(Pair l r) -> (l, r))
  . separate (uncurry Pair . first I . entangle . unI)
  . (I %)

observe1 :: (Shaped a, Shaped b, _)
         => (b -> ()) -> (a -> b) -> a -> (Demand b, Demand a)
observe1 context function input =
  runIdentity $ do
    let (input',  inputD)  = entangleShape input
        (result', resultD) = entangleShape (function input')
    !_ <- eval (context result')
    !_ <- eval (rnf inputD)
    !_ <- eval (rnf resultD)
    return (resultD, inputD)

observeNP :: (All Shaped inputs, Shaped result, _)
          => (result -> ())
          -> (NP I inputs -> result)
          -> NP I inputs
          -> ( Demand result
             , NP Demand inputs )
observeNP context function inputs =
  runIdentity $ do
    let entangled =
          hcliftA (Proxy :: Proxy Shaped)
                  (uncurry Pair . first I . entangleShape . unI) inputs
        (inputs', inputsD) =
          (hliftA (\(Pair r _) -> r) entangled,
           hliftA (\(Pair _ l) -> l) entangled)
        (result', resultD) = entangleShape (function inputs')
    !_ <- eval (context result')
    !_ <- eval (rnf inputsD)
    !_ <- eval (rnf resultD)
    return (resultD, inputsD)

observe :: (All Shaped (Args function), Shaped (Result function), _)
        => (Result function -> ())
        -> function
        -> Args function
        ⋯-> ( Demand (Result function)
             , NP Demand (Args function) )
observe context function =
  curryAll (observeNP context (uncurryAll function))


-----------------------
-- Shrinking demands --
-----------------------

shrinkDemand :: forall a. Shaped a => PosDemand a -> [PosDemand a]
shrinkDemand d =
  match @a d d $ \(Flattened un flat) _ ->
    un <$> shrinkOne flat
  where
    shrinkOne :: All Shaped xs => NP Demand xs -> [NP Demand xs]
    shrinkOne Nil = []
    shrinkOne (T :* xs) =
      (T :*) <$> shrinkOne xs
    shrinkOne ((E f :: Demand x) :* xs) =
      fmap ((:* xs) . E) (shrinkDemand @x f)
      ++ fmap (E f :* ) (shrinkOne xs)


------------------------------------
-- Evaluating demands as contexts --
------------------------------------

evaluate :: forall a. Shaped a => PosDemand a -> a -> ()
evaluate demand value =
  go @a (E demand) (I % value)
  where
    go :: forall x. Shaped x => Thunk % x -> I % x -> ()
    go T     _            = ()
    go (E d) (Wrap (I v)) =
      match @x d v $
        \(Flattened _ fieldsD) -> maybe () $
        \(Flattened _ fieldsV) ->
            rnf . hcollapse $
              hcliftA2 (Proxy :: Proxy Shaped) ((K .) . go) fieldsD fieldsV


-----------------------------
-- Pretty-printing demands --
-----------------------------

showPrettyFieldThunkS
  :: Bool -> String -> Int -> Rendered Thunk -> String -> String
showPrettyFieldThunkS _            thunk _    (RWrap Thunk)      = (thunk ++)
showPrettyFieldThunkS qualifyNames thunk prec (RWrap (Eval pd)) =
  case pd of
    ConstructorD name fields ->
      showParen (prec > 10 && length fields > 0) $
        showString (qualify name)
        . flip foldMapCompose fields
          (((' ' :) .) . showPrettyFieldThunkS qualifyNames thunk 11)
    RecordD name recfields ->
      showParen (prec > 10) $
        showString (qualify name)
        . flip foldMapCompose recfields
          (\(fName, x) ->
             ((((" " ++ qualify fName ++ " = ") ++) .) $
             showPrettyFieldThunkS qualifyNames thunk 11 x))
    InfixD name assoc fixity l r ->
      showParen (prec > fixity) $
        let (lprec, rprec) =
              case assoc of
                LeftAssociative  -> (fixity,     fixity + 1)
                RightAssociative -> (fixity + 1, fixity)
                NotAssociative   -> (fixity + 1, fixity + 1)
        in showPrettyFieldThunkS qualifyNames thunk lprec l
         . showString (" " ++ qualify name ++ " ")
         . showPrettyFieldThunkS qualifyNames thunk rprec r
    CustomD fixity list ->
      showParen (prec > fixity) $
        foldr (.) id $ flip fmap list $
          extractEither
          . bimap (showString . qualifyEither)
                  (\(f, pf) -> showPrettyFieldThunkS qualifyNames thunk f pf)
  where
    qualify (m, _, n) =
      if qualifyNames then (m ++ "." ++ n) else n

    qualifyEither (Left s) = s
    qualifyEither (Right (m, n)) =
      if qualifyNames then (m ++ "." ++ n) else n

    extractEither (Left x)  = x
    extractEither (Right x) = x

    foldMapCompose :: (a -> (b -> b)) -> [a] -> (b -> b)
    foldMapCompose f = appEndo . foldMap (Endo . f)

-- This precedence-aware pretty-printing algorithm is adapted from a solution
-- given by Brian Huffman on StackOverflow:
-- https://stackoverflow.com/questions/27471937/43639618#43639618


prettyDemand :: Shaped a => Demand a -> String
prettyDemand d =
  showPrettyFieldThunkS False "_" 0 (renderfold d) ""

printDemand :: Shaped a => Demand a -> IO ()
printDemand = putStrLn . prettyDemand

-- TODO: Comparisons module?

eqDemand :: forall a. Shaped a => Demand a -> Demand a -> Bool
eqDemand T      T      = True
eqDemand T      (E _)  = False
eqDemand (E _)  T      = False
eqDemand (E d1) (E d2) =
  match @a d1 d2 $
    \(Flattened _ flatD1) -> maybe False $
    \(Flattened _ flatD2) ->
      all id . hcollapse $
        hcliftA2 (Proxy :: Proxy Shaped)
          ((K .) . eqDemand) flatD1 flatD2
