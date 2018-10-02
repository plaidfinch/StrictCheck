{-# language DeriveTraversable #-}
{-| A 'Demand' on some value of type @T@ is shaped like a @T@, but possibly
    truncated, to represent partial evaluation. This module defines the type of
    demands, and functions to manipulate them for the purpose of constructing
    demand specifications.

    A demand for some type @T@ can be represented one of two interconvertible
    ways:

    * explicitly, as a recursively interleaved @Shape@ of @T@
    * implicitly, as a value of @T@ with specially-tagged bottom values
      which represent un-evaluated portions of that value

   The explicit representation is useful for writing traversals and other such
   manipulations of demand values, while the implicit representation can prove
   convenient for writing demand specifications. The implicit representation is
   the default when writing specifications, but through the use of 'toDemand'
   and 'fromDemand', either representation can be used wherever it is most
   appropriate.
-}
module Test.StrictCheck.Demand
  ( -- * The explicit @Demand@ interface
    Thunk(..)
  , Demand, PosDemand
  , pattern E, pattern T
  -- ** Manipulating explicit @Demand@s
  , evaluateDemand
  , shrinkDemand
  , prettyDemand, printDemand
  , eqDemand
  , showPrettyFieldThunkS
  -- * The implicit @Demand@ interface
  , thunk, isThunk
  -- * Converting between explicit and implicit representations
  , toDemand, fromDemand
  ) where

import qualified Control.Exception as Exception
import qualified GHC.Generics as GHC
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

-- | A @Thunk a@ is either an @a@ or a @Thunk@
--
-- When we interleave this type into the @Shape@ of some type, we get the type
-- of demands on that type.
--
-- @Thunk a@ is isomorphic to a (strict) @Maybe a@.
data Thunk a
  = Eval !a
  | Thunk
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, GHC.Generic)

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

-- | A @Demand@ on some type @a@ is the same shape as that original @a@, but with
-- possible @Thunk@s interleaved into it
type Demand
  = (%) Thunk

-- | A @PosDemand@ is a "strictly positive" demand, i.e. one where the topmost
-- level of the demanded value has definitely been forced
--
-- This is the one-level unwrapping of @Demand@, and is useful to express some
-- invariants in specifications
type PosDemand a
  = Shape a Demand

{-# COMPLETE E, T #-}

-- | Pattern synonym to abbreviate demand manipulation: @E a = Wrap (Eval a)@
pattern E :: Shape a Demand -> Demand a
pattern E a = Wrap (Eval a)

-- | Pattern synonym to abbreviate demand manipulation: @T = Wrap Thunk@
pattern T :: Demand a
pattern T = Wrap Thunk


------------------------
-- Implicit interface --
------------------------


-- | A bottom value (inhabiting all types) which StrictCheck interprets as
-- an unevaluated subpart of a data structure
--
-- > toDemand thunk  ==  T
-- > fromDemand T    ==  thunk
thunk :: forall a. a
thunk = Exception.throw Unevaluated

-- | Tests if a particular value is an implicit 'thunk'
--
-- In order to work, this function evaluates its input to weak-head normal form;
-- keep this in mind if you care about laziness.
isThunk :: Shaped a => a -> Bool
isThunk a =
  case toDemand a of
    T -> True
    _ -> False

-- | Given an @a@ whose substructures may contain 'thunk's (i.e. an implicit
-- demand representation), convert it to an explicit 'Demand'
--
-- Inverse to 'fromDemand'.
toDemand :: Shaped a => a -> Demand a
toDemand = interleave toThunk
  where
    {-# NOINLINE toThunk #-}
    toThunk :: a -> Thunk a
    toThunk a = unsafePerformIO $
      Exception.catch
        (let !_ = a in return (Eval a))
        (\(_ :: Unevaluated) -> return Thunk)

-- | Given an explicit @Demand@ for some type @a@, convert it to a value of type
-- @a@, substituting a 'thunk' for each 'T' found in the explicit demand
--
-- Inverse to 'toDemand'.
fromDemand :: Shaped a => Demand a -> a
fromDemand = fuse fromThunk
  where
    {-# NOINLINE fromThunk #-}
    fromThunk :: Thunk a -> a
    fromThunk (Eval a) = a
    fromThunk Thunk =
      Exception.throw Unevaluated

-----------------------
-- Shrinking demands --
-----------------------

-- | Shrink a non-zero demand (analogous to QuickCheck's @shrink@)
--
-- While QuickCheck's typical @shrink@ instances reduce the size of a value by
-- slicing off the top-most structure, @shrinkDemand@ reduces the size of a
-- demand by pruning it's deepest /leaves/. This ensures that all resultant
-- shrunken demands are strict sub-demands of the original.
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

-- | Evaluate some value of type @a@ to the degree specified by the given demand
--
-- If the demand and the value diverge (they pick a different side of a sum),
-- evaluation will stop at this point. Usually, @evaluateDemand@ is only called
-- on demands which are known to be structurally-compatible with the
-- accompanying value, although nothing really goes wrong if this is not true.
evaluateDemand :: forall a. Shaped a => PosDemand a -> a -> ()
evaluateDemand demand value =
  go @a (E demand) (I % value)
  where
    go :: forall x. Shaped x => Thunk % x -> I % x -> ()
    go T     _            = ()
    go (E d) (Wrap (I v)) =
      match @x d v $
        \(Flattened _ fieldsD) -> maybe () $
        \(Flattened _ fieldsV) ->
            foldr seq () . hcollapse $
              hcliftA2 (Proxy @Shaped) ((K .) . go) fieldsD fieldsV


-----------------------------
-- Pretty-printing demands --
-----------------------------

-- | A very general 'showsPrec' style function for printing demands
--
-- @showPrettyFieldThunkS q t p r@ returns a function @(String -> String)@ which
-- appends its input to a pretty-printed representation of a demand.
--
-- Specifically:
-- * @q@ is a boolean flag determining if names should be printed
-- as qualified
-- * @t@ is a string which is to be printed when a thunk is encountered
-- * @p@ is the precedence context of this function call
-- * @r@ is the 'Rendered Thunk' representing some demand
--
-- This is very general, but we expose it in its complexity just in case some
-- person wants to build a different pretty-printer.
--
-- The precedence-aware pretty-printing algorithm used here is adapted from a
-- solution given by Brian Huffman on StackOverflow:
-- <https://stackoverflow.com/questions/27471937/43639618#43639618>.
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

-- | Pretty-print a demand for display
prettyDemand :: Shaped a => Demand a -> String
prettyDemand d =
  showPrettyFieldThunkS False "_" 0 (renderfold d) ""

-- | Print a demand to standard output
--
-- > printDemand = putStrLn . prettyDemand
printDemand :: Shaped a => Demand a -> IO ()
printDemand = putStrLn . prettyDemand

-- TODO: Comparisons module?

-- | Determine if two demands are exactly equal
--
-- This relies on the @match@ method from the @Shaped@ instance for the two
-- demands, and does not require the underlying types to have @Eq@ instances.
-- However, this means that types whose @match@ methods are more coarse than
-- their equality will be compared differently by @eqDemand@. In particular,
-- the demand representations of functions will all be compared to be equal.
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

-- | 'Demand's are compared for equality using 'eqDemand'; see its documentation
-- for details
instance Shaped a => Eq (Demand a) where
  (==) = eqDemand
