{-| __Internal module__: This module does not make any stability guarantees, and
    may not adhere to the PVP.

    This module defines several utilities useful for shrinking demands and
    evaluations.

    Of these, only 'axialShrinks' and 'fairInterleave' are used by StrictCheck;
    nevertheless, we expose the 'DZipper' type and its associated functions in
    this internal module just in case.
-}
module Test.StrictCheck.Internal.Shrink
  ( Shrink(..)
  , axialShrinks
  , fairInterleave
  -- * CPS-based zippers through heterogeneous products
  , DZipper(..)
  , next
  , positions
  , dzipper
  , dzip
  ) where

import Generics.SOP
import Data.Functor.Product

-- Fair n-ary axial shrinking (a.k.a. *fair* generalization of shrink on tuples)

-- | Newtype allowing us to construct 'NP' n-ary products of shrinkers
newtype Shrink a
  = Shrink (a -> [a])

-- | A @DZipper@ is a suspended traversal through a non-empty 'NP' n-ary product
--
-- The position of the traversal within that product is existentially
-- quantified.
data DZipper f whole where
  DZipper :: (NP f (c : rs) -> NP f whole)
          -> f c
          -> NP f rs
          -> DZipper f whole

-- | Step one to the right in a @DZipper@, returning @Nothing@ if this is not
-- possible
next :: DZipper f whole -> Maybe (DZipper f whole)
next (DZipper _  _       Nil)  = Nothing
next (DZipper ls c (r :* rs')) =
  Just $ DZipper (ls . (c :*)) r rs'

-- | Given an n-ary product of @xs@, get a list of @DZipper@s, each focused in
-- sequence on the values of the input product
--
-- This is similar to the @duplicate@ operation on comonads.
positions :: NP f xs -> [DZipper f xs]
positions (dzipper -> mstart) =
  maybe [] go mstart
  where
    go start = start : maybe [] go (next start)

-- | Convert an n-ary product into a @DZipper@, returning @Nothing@ if the
-- input product is empty
dzipper :: NP f xs -> Maybe (DZipper f xs)
dzipper       Nil = Nothing
dzipper (c :* rs) = Just $ DZipper id c rs

-- | Collapse a @DZipper@ back into the n-ary product it represents
dzip :: DZipper f xs -> NP f xs
dzip (DZipper ls c rs) = ls (c :* rs)

-- | Given a list of shrinkers and a list of values-to-be-shrunk, generate
-- a list of shrunken lists-of-values, each inner list being one potential
-- "axis" for shrinking
--
-- That is, the first element of the result is all the ways the original
-- product could be shrunken by /only/ shrinking its first component, etc.
axialShrinks :: SListI xs => NP Shrink xs -> NP I xs -> [[NP I xs]]
axialShrinks shrinks xs =
  fmap (hliftA (\(Pair _ v) -> v) . dzip)
  . centerIter <$> positions withShrinks
  where
    iter (Pair (Shrink s) (I v)) =
      Pair (Shrink s) . I <$> (s v)

    centerIter (DZipper ls c rs) =
      map (\c' -> DZipper ls c' rs) (iter c)

    withShrinks =
      hliftA2 Pair shrinks xs

-- | Fairly interleave a list of lists in a round-robin fashion
fairInterleave :: [[a]] -> [a]
fairInterleave = roundRobin id
  where
    roundRobin k ((x : xs) : xss) = x : roundRobin (k . (xs :)) xss
    roundRobin k ([      ] : xss) = roundRobin k xss
    roundRobin k [              ] =
      case k [] of
        [ ] -> []
        xss -> roundRobin id xss
