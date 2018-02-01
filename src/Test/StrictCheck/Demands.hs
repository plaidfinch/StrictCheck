module Test.StrictCheck.Demands where

import Test.StrictCheck.Observe
import Generics.SOP
import Type.Reflection

whnf, nf, spineStrict
  :: forall a. Observe a => a -> Field Thunk a

whnf = F . E . projectD (const (F T))

nf = projectField E

spineStrict =
  unfoldD strictIfSame . I
  where
    strictIfSame :: forall x. Observe x => I x -> Thunk (Demand x I)
    strictIfSame (I x) =
      case eqTypeRep (typeOf x) (typeRep @a) of
        Nothing    -> T
        Just HRefl -> E (projectD @a I x)

data Striated a t where
  Same :: a -> Striated a a
  Diff :: t -> Striated a t

-- striate :: Field
