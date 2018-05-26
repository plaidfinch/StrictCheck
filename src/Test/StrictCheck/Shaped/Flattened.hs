{-| The @match@ function in the typeclass 'Test.StrictCheck.Shaped.Shaped'
    allows you to uniformly operate over all the fields in a given piece of
    data--for instance, consuming them, iterating over them, counting them,
    etc. This module defines a uniform representation to allow this to work.

    This is in the nitty-gritty of how StrictCheck works: you do not need to
    understand this in order to use StrictCheck, unless you need to declare
    custom instances of @Shaped@ for a type not supported by StrictCheck's
    generics mechanism (i.e. GADTs, existential types, abstract types).
|-}

module Test.StrictCheck.Shaped.Flattened where

import Generics.SOP

-- | The @Flattened@ type contains all the fields in a piece of data
-- (represented as an n-ary product 'NP' from "Generics.SOP"), paired with a way
-- to re-assemble them into a value of the original datatype.
--
-- @Flattened d f xs@ can be read as "some value of type @d f@, which has been
-- separated into an n-ary product @NP f xs@ and a function which can reconstruct
-- a value @d h@ for any @h@, given an n-ary product with matching field types
-- to the one contained here.
--
-- Pay attention to the kinds! @d :: (* -> *) -> *@, @f :: * -> *@, and
-- @xs :: [*]@.
--
-- For types which are literally a collection of fields with no extra
-- information, the reconstruction function merely converts the given list of
-- fields back into a value of the original type. For types which contain extra
-- information in their values (beyond what StrictCheck considers fields), this
-- function should contain that information, and re-attach it to the field
-- values it receives.
data Flattened d f xs where
  Flattened
    :: (forall h. NP h xs -> d h)
    -> NP f xs
    -> Flattened d f xs

-- | Use the re-assembly close in a @Flattened@ to yield a value of the original
-- type from which it was derived.
unflatten :: Flattened d f xs -> d f
unflatten (Flattened u p) = u p

-- | If all the fields in a @Flattened@ satisfy some constraint, map a function
-- expecting that constraint across all the fields. This may change the functor
-- over which the @Flattened@ value is paramaterized.
mapFlattened :: forall c d f g xs. All c xs
  => (forall x. c x => f x -> g x) -> Flattened d f xs -> Flattened d g xs
mapFlattened t (Flattened u p) =
  Flattened u (hcliftA (Proxy @c) t p)
