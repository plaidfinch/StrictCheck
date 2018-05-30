module Test.StrictCheck.Demand
  ( Thunk(..)
  , Demand, PosDemand
  , pattern E, pattern T
  , thunk, isThunk
  , toDemand, fromDemand
  , evaluate
  , shrinkDemand
  , prettyDemand, printDemand
  , showPrettyFieldThunkS
  ) where

import qualified Control.Exception as Exception
import qualified GHC.Generics as GHC
import Control.DeepSeq
import Control.Applicative
import Data.Bifunctor
import System.IO.Unsafe
import Data.Monoid ( Endo(..) )
import Generics.SOP hiding (Shape)

import Test.StrictCheck.Shaped
import Test.StrictCheck.Internal.Unevaluated

--------------------------------------------------------
-- The basic types which make up a demand description --
--------------------------------------------------------

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

thunk :: forall a. a
thunk = Exception.throw Unevaluated

isThunk :: Shaped a => a -> Bool
isThunk a =
  case toDemand a of
    T -> True
    _ -> False

toDemand :: Shaped a => a -> Demand a
toDemand = interleave toThunk
  where
    toThunk :: a -> Thunk a
    toThunk a = unsafePerformIO $
      (Eval <$> Exception.evaluate a)
      `Exception.catch`
      (\(_ :: Unevaluated) -> return Thunk)

fromDemand :: Shaped a => Demand a -> a
fromDemand = fuse fromThunk
  where
    fromThunk :: Thunk a -> a
    fromThunk (Eval a) = a
    fromThunk Thunk =
      Exception.throw Unevaluated

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
              hcliftA2 (Proxy @Shaped) ((K .) . go) fieldsD fieldsV


-----------------------------
-- Pretty-printing demands --
-----------------------------

showPrettyFieldThunkS
  :: Bool -> String -> Int -> Rendered Thunk -> String -> String
showPrettyFieldThunkS _            t _    (RWrap Thunk)      = (t ++)
showPrettyFieldThunkS qualifyNames t prec (RWrap (Eval pd)) =
  case pd of
    ConstructorD name fields ->
      showParen (prec > 10 && length fields > 0) $
        showString (qualify name)
        . flip foldMapCompose fields
          (((' ' :) .) . showPrettyFieldThunkS qualifyNames t 11)
    RecordD name recfields ->
      showParen (prec > 10) $
        showString (qualify name)
        . flip foldMapCompose recfields
          (\(fName, x) ->
             ((((" " ++ qualify fName ++ " = ") ++) .) $
             showPrettyFieldThunkS qualifyNames t 11 x))
    InfixD name assoc fixity l r ->
      showParen (prec > fixity) $
        let (lprec, rprec) =
              case assoc of
                LeftAssociative  -> (fixity,     fixity + 1)
                RightAssociative -> (fixity + 1, fixity)
                NotAssociative   -> (fixity + 1, fixity + 1)
        in showPrettyFieldThunkS qualifyNames t lprec l
         . showString (" " ++ qualify name ++ " ")
         . showPrettyFieldThunkS qualifyNames t rprec r
    CustomD fixity list ->
      showParen (prec > fixity) $
        foldr (.) id $ flip fmap list $
          extractEither
          . bimap (showString . qualifyEither)
                  (\(f, pf) -> showPrettyFieldThunkS qualifyNames t f pf)
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
        hcliftA2 (Proxy @Shaped)
          ((K .) . eqDemand) flatD1 flatD2

instance Shaped a => Eq (Demand a) where
  (==) = eqDemand
