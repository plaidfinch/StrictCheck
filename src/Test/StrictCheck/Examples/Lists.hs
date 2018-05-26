module Test.StrictCheck.Examples.Lists where

import Test.StrictCheck
import Control.DeepSeq
import Data.Functor

length_spec :: Shaped a => Spec '[[a]] Int
length_spec =
  Spec $ \predict _ xs ->
    predict (xs $> thunk)

take' :: Int -> [a] -> [a]
take' _      [] = []
take' n (x : xs)
  | n > 0     = x : take' (n-1) xs
  | otherwise = []

take_spec_too_easy :: Shaped a => Spec '[Int, [a]] [a]
take_spec_too_easy =
  Spec $ \predict _d n xs ->
    predict n xs

take_spec :: Shaped a => Spec '[Int, [a]] [a]
take_spec =
  Spec $ \predict d n xs ->
    predict n (if n > length xs then d else d ++ thunk)

map_spec
  :: forall a b. (Shaped a, Shaped b, NFDemand a, NFDemand b)
  => Spec '[a -> b, [a]] [b]
map_spec =
  Spec $ \predict d f xs ->
    predict
      (if all isThunk (cap d) then thunk else f)
      (zipWith (specify1 f) d xs)

replaceThunk :: Shaped a => [a] -> [a] -> [a]
replaceThunk r xs       | isThunk xs = r
replaceThunk _ [      ] = []
replaceThunk r (x : xs) = x : replaceThunk r xs

cap :: Shaped a => [a] -> [a]
cap = replaceThunk []

-- TODO: fixities

(%$) :: (Shaped a, Shaped b) => (a -> b) -> Demand a -> Demand b
(%$) f = toDemand . f . fromDemand

(%*) :: (Shaped a, Shaped b) => Demand (a -> b) -> Demand a -> Demand b
f %* a = toDemand $ fromDemand f (fromDemand a)

-- TODO: write this
-- replaceThunk :: (Shaped a, Shaped b) => a -> b -> a
-- replaceThunk = undefined

type NFDemand a = NFData (Shape a Demand)

-- TODO: make n-ary version of this (CPS-ed)
specify1 :: forall a b. (Shaped a, Shaped b , NFDemand a, NFDemand b)
         => (a -> b) -> b -> a -> a
specify1 f b a =
  fromDemand . snd $ observe1 (toContext b) f a

toContext :: Shaped b => b -> b -> ()
toContext b =
  case toDemand b of
    T    -> const ()
    E b' -> evaluate b'

rotate :: [a] -> [a] -> [a] -> [a]
rotate [      ] [      ] as =                       as
rotate [      ] (b : bs) as =     rotate [] bs (b : as)
rotate (f : fs) [      ] as = f : rotate fs []      as
rotate (f : fs) (b : bs) as = f : rotate fs bs (b : as)

rot :: [a] -> [a] -> [a]
rot fs bs = rotate fs bs []

rot' :: [a] -> [a] -> [a]
rot' fs bs = fs ++ reverse bs

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

-- Leo: Still not working...
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

expectTotal :: Shaped a => a -> a
expectTotal a =
  if isThunk a then error "expectTotal: given thunk" else a

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

reverse_spec :: Shaped a => Spec '[[a]] [a]
reverse_spec =
  Spec $ \predict d xs ->
    let padLen = length xs - length (cap d)
        spinePad = replicate padLen thunk
    in  predict $ spinePad ++ (reverse (cap d))

zip' :: [a] -> [b] -> [(a, b)]
zip' [      ] [      ] = []
zip' (_ : as) [      ] = zip' as []
zip' [      ] (_ : bs) = zip' [] bs
zip' (a : as) (b : bs) = (a, b) : zip' as bs

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
