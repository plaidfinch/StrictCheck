module Test.StrictCheck.Examples.Lists where

import Test.StrictCheck
import Control.DeepSeq
import Data.List

instance Show (a -> b) where show _ = "<function>"

take_spec :: Shaped a => Spec '[Int, [a]] [a]
take_spec =
  Spec $ \predict d n xs ->
    predict n (if n > length xs then d else d ++ thunk)

map_spec
  :: forall a b. (Shaped a, Shaped b, NFDemand a, NFDemand b)
  => Spec '[a -> b, [a]] [b]
map_spec =
  Spec $ \predict d f xs ->
    predict (if all isThunk (appendListDemand d []) then thunk else f)
            (zipWith (specify1 f) d xs)

appendListDemand :: Shaped a => [a] -> [a] -> [a]
appendListDemand xs       ys | isThunk xs = ys
appendListDemand [      ] ys = ys
appendListDemand (x : xs) ys = x : appendListDemand xs ys

-- TODO: write this
-- replace :: (Shaped a, Shaped b) => a -> b -> a
-- replace = undefined

type NFDemand a = NFData (Shape a Demand)

-- TODO: make n-ary version of this (CPS-ed)
specify1
  :: forall a b.
  ( Shaped a, Shaped b , NFDemand a, NFDemand b
  ) => (a -> b) -> b -> a -> a
specify1 f d a =
  fromDemand . snd $ observe1 context f a
  where
    context :: b -> ()
    context = case toDemand d of
      T    -> const ()
      E d' -> evaluate @b d'

rotate :: [a] -> [a] -> [a] -> [a]
rotate []            []  as =                       as
rotate []       (b : bs) as =     rotate [] bs (b : as)
rotate (f : fs)      []  as = f : rotate fs []      as
rotate (f : fs) (b : bs) as = f : rotate fs bs (b : as)

rot :: [a] -> [a] -> [a]
rot fs bs = rotate fs bs []

rot_spec :: Shaped a => Spec '[[a], [a]] [a]
rot_spec =
  Spec $ \predict d fs bs ->
    let (fs', bs') = splitAt (length fs) d
        ontoD   = appendListDemand d
        ontoFs' = appendListDemand fs'
        ontoBs' = appendListDemand bs'
    in predict
         (fs' ++
         if length (ontoD []) > length fs
         then []
         else thunk)
         (reverse (ontoBs' (replicate (length bs - length (ontoBs' [])) thunk))
         ++ (if length (ontoD []) > length fs + length bs
             || length (ontoD []) + length bs == 0
             then []
             else thunk))
