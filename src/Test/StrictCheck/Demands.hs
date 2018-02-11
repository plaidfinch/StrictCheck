module Test.StrictCheck.Demands where

import Generics.SOP hiding ( Shape )
import Type.Reflection

import Test.StrictCheck.Observe
import Test.StrictCheck.Shaped

whnf, nf, spineStrict
  :: forall a. Shaped a => a -> Demand a

whnf = Wrap . E . project (const (Wrap T))

nf = interleave E

spineStrict =
  extrafold strictIfSame . I
  where
    strictIfSame :: forall x. Shaped x => I x -> Thunk (Shape x I)
    strictIfSame (I x) =
      case eqTypeRep (typeOf x) (typeRep @a) of
        Nothing    -> T
        Just HRefl -> E (project @a I x)

data Striated a t where
  Same :: a -> Striated a a
  Diff :: t -> Striated a t

-- striate :: Field
