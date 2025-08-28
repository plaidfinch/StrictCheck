{-| This module defines a variety of specifications for functions on lists,
    demonstrating the specification interface of StrictCheck. See the
    documentation of "Test.StrictCheck" (specifically 'strictCheckSpecExact')
    for details on how to test these specifications.

    This module's primary utility is to teach how specifications work. Because
    Haddock omits the definitions of values, you'll learn the most by viewing
    the source of this module.
-}
module Test.StrictCheck.Examples.Lists where

import Test.StrictCheck
import Data.Functor (($>))

-- * Specifying some simple functions on lists

-- | A correct specification for 'length'
length_spec :: Spec '[[a]] Int
length_spec =
  Spec $ \predict _ xs ->
    predict (xs $> thunk)

-- | An incorrect specification for 'length' (to test the pretty printer)
bad_length_spec :: Spec '[[a]] Int
bad_length_spec =
  Spec $ \predict _ xs ->
    predict (take 1 xs $> thunk)

-- | A naive specification for 'take', which is wrong
take_spec_too_easy :: Spec '[Int, [a]] [a]
take_spec_too_easy =
  Spec $ \predict _d n xs ->
    predict n xs

-- | A correct specification for 'take'
take_spec :: Spec '[Int, [a]] [a]
take_spec =
  Spec $ \predict d n xs ->
    predict n (if n > length xs then d else d ++ thunk)

-- | A functionally correct implementation of 'take' which has subtly different
-- strictness properties
--
-- This will fail when tested against 'take_spec'.
take' :: Int -> [a] -> [a]
take' _      [] = []
take' n (x : xs)
  | n > 0     = x : take' (n-1) xs
  | otherwise = []

-- | A correct specification of '(++)'
append_spec :: Shaped a => Spec '[[a], [a]] [a]
append_spec =
  Spec $ \predict d ls rs ->
    let spineLen   = length . cap $ d ++ [undefined]  -- number of spine thunks forced
        overLs     = spineLen > length ls             -- forced all of ls?
        overRs     = spineLen > length ls + length rs -- forced all of bs?
        (ls', rs') = splitAt (length ls) (cap d)
    in predict
         (ls' ++ if overLs then [] else thunk)
         (rs' ++ if overRs then [] else thunk)

-- | A correct specification of 'reverse'
reverse_spec :: Shaped a => Spec '[[a]] [a]
reverse_spec =
  Spec $ \predict d xs ->
    let padLen = length xs - length (cap d)
        spinePad = replicate padLen thunk
    in  predict $ spinePad ++ (reverse (cap d))

-- | A correct specification for 'zip'
zip_spec :: (Shaped a, Shaped b) => Spec '[[a], [b]] [(a, b)]
zip_spec =
  Spec $ \predict d as bs ->
    let (d_as, d_bs) = unzip d
    in predict
         (if      length (cap d_bs) > length as
          && not (length (cap d_as) > length bs)
          then d_as
          else d_as ++ thunk)
         (if length (cap d_as) > length bs
          && not (length (cap d_bs) > length as)
          then d_bs
          else d_bs ++ thunk)

-- | A functionally correct implementation of 'zip' which has subtly different
-- strictness properties
--
-- This will fail when tested against 'zip_spec'.
zip' :: [a] -> [b] -> [(a, b)]
zip' [      ] [      ] = []
zip' (_ : as) [      ] = zip' as []
zip' [      ] (_ : bs) = zip' [] bs
zip' (a : as) (b : bs) = (a, b) : zip' as bs

-- | A correct specification for 'map', demonstrating specifications for
-- higher-order functions
map_spec
  :: forall a b. (Shaped a, Shaped b)
  => Spec '[a -> b, [a]] [b]
map_spec =
  Spec $ \predict d f xs ->
    predict
      (if all isThunk (cap d) then thunk else f)
      (zipWith (specify1 f) d xs)

-- * Specifying the productive rotate function from Okasaki's purely functional
-- queue implementation (see paper for more details)

-- | Given three lists @xs@, @ys@, and @zs@, compute @xs ++ reverse ys ++ zs@,
-- but with more uniform strictness
--
-- Specifically, if @ys@ is shorter than @xs@, the work necessary to reverse it
-- will have already occurred by the time @xs@ is traversed.
rotate :: [a] -> [a] -> [a] -> [a]
rotate [      ] [      ] as =                       as
rotate [      ] (b : bs) as =     rotate [] bs (b : as)
rotate (f : fs) [      ] as = f : rotate fs []      as
rotate (f : fs) (b : bs) as = f : rotate fs bs (b : as)

-- | Specialization of 'rotate': @rot xs ys = rotate xs ys []@
rot :: [a] -> [a] -> [a]
rot fs bs = rotate fs bs []

-- | The naive version of 'rot': @rot' xs ys = xs ++ reverse ys@
--
-- This is functionally equivalent to 'rot' but not equivalent in strictness
-- behavior.
rot' :: [a] -> [a] -> [a]
rot' fs bs = fs ++ reverse bs

-- | A previous iteration of `rot_spec'`, this one is also correct, but may be
-- less readable.
rot_spec :: Shaped a => Spec '[[a], [a]] [a]
rot_spec =
  Spec $ \predict d fs bs ->
    let (fs', bs') = splitAt (length fs) (cap d)
        spineLen  = length (cap (d ++ [undefined]))  -- # of spine thunks forced
        overflow  = spineLen       > length fs  -- begun taking from bs?
        overrot   = length (cap d) > length bs  -- forced all of bs?
        padLength =
          length bs `min`
            if overflow
            then length bs - length bs'
            else length (cap d)
        spinePad = replicate padLength thunk
    in predict
         (                    fs' ++ if overflow            then [] else thunk)
         (spinePad ++ reverse bs' ++ if overflow || overrot then [] else thunk)

-- | A correct specification of `rot`, this is also the version we presented in
-- the paper.
rot_spec' :: Shaped a => Spec '[[a], [a]] [a]
rot_spec' =
  Spec $ \predict d fs bs ->
    let demandOnFs
          | length (cap d) > length fs =
              take (length fs) (cap d)
          | otherwise = d
        demandOnBs
          | length (cap $ d ++ [undefined]) > length fs =
              reverse $ take (length bs)
                      $ drop (length fs) (cap d) ++ repeat thunk
          | length (cap d) > length bs =
              reverse $ drop (length fs) (cap d) ++ replicate (length bs) thunk
          | otherwise =
              (reverse $ drop (length fs) (cap d) ++ replicate (length (cap d)) thunk) ++ thunk
    in predict demandOnFs demandOnBs
--   where predictedFsDemand
--           | outputDemandLength < length fs =
--               outputDemand ++ thunk
--           | otherwise =
--               fsPartOfOutDemand
--         predictedBsDemand
--           | outputDemandLength < length bs =
--
--           | otherwise =
--
--     let (fs', bs') = splitAt (length fs) (cap d)
--         spineLen  = length (cap (d ++ [undefined]))  -- # of spine thunks forced
--         overflow  = spineLen       > length fs  -- begun taking from bs?
--         overrot   = length (cap d) > length bs  -- forced all of bs?
--         padLength =
--           length bs `min`
--             if overflow
--             then length bs - length bs'
--             else length (cap d)
--         spinePad = replicate padLength thunk
--     in predict
--          (                    fs' ++ if overflow            then [] else thunk)
--          (spinePad ++ reverse bs' ++ if overflow || overrot then [] else thunk)

--rot_spec' :: Shaped a => Spec '[[a], [a]] [a]
--rot_spec' = rot_spec

-- | An incorrect specification for `rot` that miscalculates the number of cells
-- forced.
rot_simple_spec :: Shaped a => Spec '[[a], [a]] [a]
rot_simple_spec =
  Spec $ \predict d fs bs ->
    let demandOnFs
          | length (cap d) > length fs =
              take (length fs) d
          | otherwise = d
        demandOnBs
          | length (cap d) > length fs ||
            (null bs && length fs == length (cap d) && length fs /= length (cap $ d ++ [thunk])) =
              reverse $ take (length bs) $ (drop (length fs) (cap d)) ++ repeat thunk
          | otherwise =
              thunk
    in predict demandOnFs demandOnBs

test_rot :: [Int] -> [Int] -> [Int] -> IO ()
test_rot d xs ys =
  (\(x :* y :* Nil) -> printDemand x >> printDemand y)
  . snd $ observe (toContext d) (rot @Int) xs ys

-- * Utilities for working with demands over lists

-- | If the tail of the second list is 'thunk', replace it with the first list
replaceThunk :: Shaped a => [a] -> [a] -> [a]
replaceThunk r xs       | isThunk xs = r
replaceThunk _ [      ] = []
replaceThunk r (x : xs) = x : replaceThunk r xs

-- | If the tail of the list is 'thunk', replace it with @[]@
--
-- This is a special case of 'replaceThunk'.
cap :: Shaped a => [a] -> [a]
cap = replaceThunk []

-- | Lift an ordinary function to apply to explicit 'Demand's
--
-- It is true that @Demand@s are a functor, but they can't be a Haskell
-- 'Functor' because they're a type family
(%$) :: (Shaped a, Shaped b) => (a -> b) -> Demand a -> Demand b
(%$) f = toDemand . f . fromDemand

-- | Apply a 'Demand' on a function to a 'Demand' on a value
--
-- It is true that @Demand@s are an applicative functor, but they can't be a
-- Haskell 'Functor' because they're a type family
(%*) :: (Shaped a, Shaped b) => Demand (a -> b) -> Demand a -> Demand b
f %* a = toDemand $ fromDemand f (fromDemand a)

-- TODO: make n-ary version of this (CPS-ed)
-- | Given a unary function, an implicit demand on its result, and its input,
-- compute its actual demand on its input in that context
--
-- This demand is calculated using 'observe1', so it is guaranteed to be
-- correct.
specify1 :: forall a b. (Shaped a, Shaped b)
         => (a -> b) -> b -> a -> a
specify1 f b a =
  fromDemand . snd $ observe1 (toContext b) f a

-- | Given an implicit demand, convert it to an evaluation context
--
-- That is, @toContext d a@ evaluates @a@ to the degree that @d@ is a defined
-- value. This uses the function 'evaluateDemand'; refer to its documentation
-- for details about how demands are used to evaluate values.
toContext :: Shaped b => b -> b -> ()
toContext b =
  case toDemand b of
    T    -> const ()
    E b' -> evaluateDemand b'

-- | Assert at runtime that a value is /not/ a 'thunk', failing with an error
-- if it is
expectTotal :: Shaped a => a -> a
expectTotal a =
  if isThunk a then error "expectTotal: given thunk" else a
