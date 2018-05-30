module Test.StrictCheck.Instances.Tools
  ( Containing(..)
  , projectContainer
  , embedContainer
  , Prim(..), unPrim
  , projectPrim
  , embedPrim
  , matchPrim
  , flatPrim
  , renderPrim
  , renderConstant
  ) where

import Control.DeepSeq

import Generics.SOP
import GHC.Generics as GHC

import Test.StrictCheck.Shaped

-- | The @Shape@ of a spine-strict container (i.e. a @Map@ or @Set@) is the same
-- as a container of demands on its elements. However, this does not have the
-- right /kind/ to be used as a @Shape@.
--
-- The @Containing@ newtype solves this problem. By defining the @Shape@ of some
-- container @(C a)@ to be @(C `Containing` a)@, you can use the methods
-- @projectContainer@ and @embedContainer@ to implement @project@ and @embed@
-- for your container type (although you will still need to manually define
-- @match@ and @render@).
newtype Containing h a f =
  Container (h (f a))
  deriving (Eq, Ord, Show, GHC.Generic)
  deriving newtype NFData

-- | Generic implementation of @project@ for any container type whose @Shape@
-- is represented as a @Containing@ newtype
projectContainer :: (Functor c, Shaped a)
  => (forall x. Shaped x => x -> f x)
  -> c a -> Containing c a f
projectContainer p x  = Container (fmap p x)

-- | Generic implementation of @embed@ for any container type whose @Shape@
-- is represented as a @Containing@ newtype
embedContainer :: (Functor c, Shaped a)
  => (forall x. Shaped x => f x -> x)
  -> Containing c a f -> c a
embedContainer e (Container x) = fmap e x


-- TODO: helper functions for matching and prettying containers

-- | The @Shape@ of a primitive type should be equivalent to the type itself.
-- However, this does not have the right /kind/ to be used as a @Shape@.
--
-- The @Prim@ newtype solves this problem. By defining the @Shape@ of some
-- primitive type @p@ to be @Prim p@, you can use the methods @projectPrim@,
-- @embedPrim@, @matchPrim@, and @prettyPrim@ to completely fill in the
-- definition of the @Shaped@ class for a primitive type.
--
-- __Note:__ It is only appropriate to use this @Shape@ representation when a
-- type really is primitive, in that it contains no interesting substructure.
-- If you use the @Prim@ representation inappropriately, StrictCheck will not be
-- able to inspect the richer structure of the type in question.
newtype Prim (x :: *) (f :: * -> *) = Prim x
  deriving (Eq, Ord, Show, GHC.Generic)
  deriving newtype (NFData, Num)

-- | Get the wrapped @x@ out of a @Prim x f@ (inverse to the @Prim@ constructor)
unPrim :: Prim x f -> x
unPrim (Prim x) = x

-- | Generic implementation of @project@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype
projectPrim :: (forall x. Shaped x => x -> f x) -> a -> Prim a f
projectPrim _ = Prim

-- | Generic implementation of @embed@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype
embedPrim :: (forall x. Shaped x => f x -> x) -> Prim a f -> a
embedPrim _ = unPrim

-- | Generic implementation of @match@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype with an underlying @Eq@ instance
matchPrim :: Eq a => Prim a f -> Prim a g
           -> (forall xs. All Shaped xs
                => Flattened (Prim a) f xs
                -> Maybe (Flattened (Prim a) g xs)
                -> result)
           -> result
matchPrim (Prim a) (Prim b) k =
  k (flatPrim a)
     (if a == b then (Just (flatPrim b)) else Nothing)

-- | Helper for writing @match@ instances for primitive types which don't have
-- @Eq@ instance
--
-- This generates a @Flattened@ appropriate for using in the implementation of
-- @match@. For more documentation on how to use this, see the documentation of
-- 'match'.
flatPrim :: a -> Flattened (Prim a) g '[]
flatPrim x = Flattened (const (Prim x)) Nil

-- | Generic implementation of @render@ for any primitive type whose @Shape@ is
-- is represented as a @Prim@ newtype
renderPrim :: Show a => Prim a (K x) -> RenderLevel x
renderPrim (Prim a) = renderConstant (show a)

-- | Given some @string@, generate a custom pretty-printing representation which
-- just shows the string
renderConstant :: String -> RenderLevel x
renderConstant s = CustomD 11 [Left (Left s)]


-- TODO: What about demands for abstract types with > 1 type of unbounded-count field?

-- withFieldsContainer ::
--   forall c a f result.
--      (forall r h.
--         c (h a) ->
--         (forall x. Shaped x
--            => [h x]
--            -> (forall g. [g x] -> c (g a))
--            -> r)
--         -> r)
--   -> Containing c a f
--   -> (forall xs. All Shaped xs
--         => NP f xs
--         -> (forall g. NP g xs -> Containing c a g)
--         -> result)
--   -> result
-- withFieldsContainer viaContaining (Container c) cont =
--   viaContaining c $
--     \list un ->
--        withNP @Shaped list (Container . un) cont

-- TODO: Make this work for any number of lists of fields, by carefully using
-- unsafeCoerce to deal with unknown list lengths
{-
withFieldsViaList ::
  forall demand f result.
     (forall r h.
        demand h ->
        (forall x. Shaped x
           => [h x]
           -> (forall g. [g x] -> demand g)
           -> r)
        -> r)
  -> demand f
  -> (forall xs. All Shaped xs
        => NP f xs
        -> (forall g. NP g xs -> demand g)
        -> result)
  -> result
withFieldsViaList viaList demand cont =
  viaList demand $
    \list un ->
       withNP @Shaped list un cont

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
-}
