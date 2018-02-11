module Test.StrictCheck.Shaped.Flattened where

import Generics.SOP

data Flattened d f xs where
  Flattened
    :: (forall h. NP h xs -> d h)
    -> NP f xs
    -> Flattened d f xs

unflatten :: Flattened d f xs -> d f
unflatten (Flattened u p) = u p

mapFlattened :: forall c d f g xs. All c xs
  => (forall x. c x => f x -> g x) -> Flattened d f xs -> Flattened d g xs
mapFlattened t (Flattened u p) =
  Flattened u (hcliftA (Proxy :: Proxy c) t p)
