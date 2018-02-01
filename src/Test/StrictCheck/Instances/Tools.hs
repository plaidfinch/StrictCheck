module Test.StrictCheck.Instances.Tools where

import Test.StrictCheck.Observe
import Generics.SOP

-- TODO: What about demands for abstract types with > 1 type of unbounded-count field?

withFieldsViaList ::
  forall demand f result.
     (forall r h.
        demand h ->
        (forall x. Observe x
           => [f x]
           -> (forall g. [g x] -> demand g)
           -> r)
        -> r)
  -> demand f
  -> (forall xs. All Observe xs
        => NP f xs
        -> (forall g. NP g xs -> demand g)
        -> result)
  -> result
withFieldsViaList viaList demand cont =
  viaList demand $
    \list unflatten ->
       withNP @Observe list unflatten cont

withNP :: forall c demand result f x. c x
       => [f x]
       -> (forall g. [g x] -> demand g)
       -> (forall xs. All c xs
             => NP f xs -> (forall g. NP g xs -> demand g) -> result)
       -> result
withNP list unList cont =
  withUnhomogenized @c list $ \np ->
    cont np (unList . homogenize)

withConcatenated :: NP (NP f) xss -> (forall xs. NP f xs -> r) -> r
withConcatenated pop cont =
  case pop of
    Nil         -> cont Nil
    (xs :* xss) -> withConcatenated xss (withPrepended xs cont)
  where
    withPrepended ::
      NP f ys -> (forall zs. NP f zs -> r)
              -> (forall zs. NP f zs -> r)
    withPrepended pre k rest =
      case pre of
        Nil        -> k rest
        (x :* xs)  -> withPrepended xs (k . (x :*)) rest

homogenize :: All ((~) a) as => NP f as -> [f a]
homogenize      Nil  = []
homogenize (a :* as) = a : homogenize as

withUnhomogenized :: forall c a f r.
  c a => [f a] -> (forall as. (All c as, All ((~) a) as) => NP f as -> r) -> r
withUnhomogenized      []  k = k Nil
withUnhomogenized (a : as) k =
  withUnhomogenized @c as $ \np -> k (a :* np)
