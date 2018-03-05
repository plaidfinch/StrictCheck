module Test.StrictCheck.Examples.Lists where

import Test.StrictCheck

import Generics.SOP

pattern (:%) :: Demand a -> Demand [a] -> PosDemand [a]
pattern x :% xs = GS (S (Z (x :* xs :* Nil)))

pattern Nil' :: PosDemand [a]
pattern Nil' = GS (Z Nil)

{-# COMPLETE (:%), Nil' #-}

take_spec :: Shaped a => Spec '[Int, [a]] [a]
take_spec =
  Spec $ \predict d n xs ->
    predict
      (nf n)
      (if n > length xs then E d else endThunk d)
      -- (if n > length xs
      --  then E d
      --  else replace (E Nil') T (E d))
  where
    endThunk :: PosDemand [a] -> Demand [a]
    endThunk = \case
      Nil'        -> T
      dx :% T     -> E (dx :% T)
      dx :% E dxs -> E (dx :% endThunk dxs)

    -- TODO: rephrase with reshape?
