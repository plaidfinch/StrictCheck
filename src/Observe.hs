{-# language TypeInType, ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, BangPatterns #-}

------------------------------------------------------------------------
-- Observing the strictness of Haskell functions from within Haskell! --
------------------------------------------------------------------------

module Observe where

import System.IO.Unsafe
import Control.Spoon
import Data.Coerce
import Data.Foldable
import Data.Maybe
import Data.IORef
import Data.Functor.Identity
import Data.Functor.Classes
import Control.DeepSeq
import Data.Kind
import Data.List

-- NOTE: In this module, we specialize to functions on lists (of primitives).
-- The end goal is to turn this into a generic programming library which lets
-- us do the same thing functions of any number of arguments, on any data types.

-- TODO: use pseq instead of seq to ensure that no matter what funny business
-- users do with parallelism in their input functions, our machinery works.

--------------------------------------------------------------------------------
-- Some useful contexts for testing demand

type Context a = a -> ()

lazy :: Context [a]
lazy = const ()

whnf :: Context [a]
whnf = flip seq ()

spineStrict :: Context [a]
spineStrict = flip seq () . foldl' (flip (:)) []

allStrict :: NFData a => Context [a]
allStrict = rnf

oddStrict :: NFData a => Context [a]
oddStrict []           = ()
oddStrict [x]          = rnf x
oddStrict (x : _ : xs) = rnf x `seq` oddStrict xs

evenStrict :: NFData a => Context [a]
evenStrict []           = ()
evenStrict [_]          = ()
evenStrict (_ : x : xs) = rnf x `seq` evenStrict xs


-- Combine contexts to demand the union of their demands
(!!!) :: Context a -> Context a -> Context a
(!!!) c d = \a -> c a `seq` d a

--------------------------------------------------------------------------------

-- Basic observation in GHCi of how a list gets forced

{-# NOINLINE instrumentList #-}
instrumentList :: Show a => [a] -> [a]
instrumentList [] =
  unsafePerformIO (putStrLn "[]") `seq` []
instrumentList (x : xs) =
  unsafePerformIO (putStrLn $ show x ++ " : ")
    `seq` x : instrumentList xs

--------------------------------------------------------------------------------
-- Counting the number of cons-cells forced by supplying successively more well-
-- defined inputs to a function and finding out when it. This procedure takes
-- quadratic time to complete, as it re-evaluates the input function n times,
-- where n is the amount of the input list f requires to produce its output.
-- Because we know that f must be at least O(n), demandCount must be O(n^2).

-- This technique is taken from:
-- http://math.andrej.com/2006/03/27/sometimes-all-functions-are-continuous/

{-# NOINLINE decreasingBottoms #-}
decreasingBottoms :: [a] -> [[a]]
decreasingBottoms as =
  fmap (zipWith const as) unitBottoms
    where
      unitBottoms = undefined : map (() :) unitBottoms


{-# NOINLINE demandCount #-}
demandCount :: Context b -> ([a] -> b) -> [a] -> Int
demandCount c f as = fromJust . asum $
  map fstIfDefined $
        zip [0..] $ fmap (c . f) (decreasingBottoms as)
    where
      fstIfDefined :: (Int, b) -> Maybe Int
      fstIfDefined = fmap fst . sequenceA . fmap teaspoon

-- NOTE: Notice the arguments we pass to demandCount. They are, in order:
-- a Context for b, a function from [a] -> b, and a [a]. We needn't separate
-- the Context from the function, but it makes it much more clear what the
-- intention is when using the function.

--------------------------------------------------------------------------------
-- To prevent the quadratic evaluation issue above, we instead instrument the
-- input to the function so that it updates a count stored in a single IORef.
-- This method is also described briefly in the article linked above.

{-# NOINLINE instrumentListR #-}
instrumentListR :: IORef Int -> [a] -> [a]
instrumentListR count [] = []
instrumentListR count (a : as) =
  unsafePerformIO $ do
    atomicModifyIORef' count (\x -> (succ x, ()))
    return $ a : instrumentListR count as

{-# NOINLINE demandCount' #-}
demandCount' :: Context b -> ([a] -> b) -> [a] -> Int
demandCount' c f as =
  unsafePerformIO $ do
    count <- newIORef 0
    evaluate $ c . f $ instrumentListR count as
    readIORef count

-- NOTE: A particular pattern in these kind of functions is the use of a single
-- do-block encased in a single unsafePerformIO. This limits the degree to which
-- we can get confused about sequencing of operations. If we need to ensure that
-- a particular value gets evaluated (to whnf) before we continue with the IO,
-- we can say "() <- return $! ...". The pattern match on () doesn't change the
-- strictness behavior here; it just makes sure that you're not accidentally
-- whnf-ing something with structure (you shouldn't be!). I've wrapped up this
-- idiom below:

evaluate :: () -> IO ()
evaluate !() = return ()

--------------------------------------------------------------------------------
-- However, just knowing the number of cons-cells forced in evaluation does not
-- always give us all the information we need. For instance, it tells us nothing
-- about the strictness of the function on the elements of the list. For more
-- complex data structures (e.g. trees), a single count of evaluations is quite
-- insufficient to reason about deep laziness.

-- What we need is a representation of a *demand* on a data structure, reified.
-- A demand on some ADT is that same ADT, but modified to interleave a Maybe in
-- every field of every data constructor. Demand on primitives is isomorphic to
-- unit.

-- The structure of a demand structure is:
-- For each type parameter of the original data structure, take a corresponding
-- type parameter representing the demand for that parameter. Each demand also
-- takes a final parameter representing the wrapper around each field: for
-- the internal mutable structures used in the implementation of our library,
-- this will be IORef; for the user-facing interface, this will be Identity.

-- TODO: f will *only* ever need to be instantiated at IORef and Identity.
-- It probably makes sense to just use two data structures, thus eliding the
-- Identity from the user's view of the world.

-- NOTE: Based on the structure of these types, we can certainly generically
-- derive their corresponding demand types. We should also be able to derive
-- Show, Eq, and Arbitrary instances, necessary for QuickCheck.

-- TODO: This definition is subtly wrong, in that it cannot represent or
-- instrument whether a nil constructor is forced. We need another case in
-- the ADT for ListDemand which contains a (f (Maybe (PrimDemand f)))

data ListDemand (d :: (* -> *) -> *) (f :: * -> *) =
  Cons (f (Maybe (d f)))
       (f (Maybe (ListDemand d f)))

showDemand_primList :: Maybe (ListDemand PrimDemand Identity) -> String
showDemand_primList Nothing = "…"
showDemand_primList (Just list) =
  "[" ++ intercalate ", " (go list) ++ ", …"
  where
    go (Cons (Identity x) (Identity xs)) =
      let xs' = fromMaybe [] (go <$> xs)
          x' = case x of
                 Just Demanded -> "■"
                 Nothing       -> "_"
      in x' : xs'

printDemand_primList = putStrLn . showDemand_primList

data PrimDemand f = Demanded deriving Show

-- Some other example demands:

data PairDemand xd yd f =
  PairDemand (f (Maybe (xd f)))
             (f (Maybe (yd f)))

type ListOfPairsOfIntsDemand =
       ListDemand (PairDemand PrimDemand PrimDemand) Maybe

-- Calculate the demand on the list as when f is run on it in the context c

{-# NOINLINE demandList #-}
demandList :: Context b -> ([a] -> b) -> [a]
           -> Maybe (ListDemand PrimDemand Identity)
demandList c f as =
  unsafePerformIO $ do
    topDemand <- newIORef Nothing
    evaluate $ c . f $ instrumentListD topDemand as
    traverse derefDemand =<< readIORef topDemand

-- Recursively traverse a pointer-based demand and freeze it into an immutable
-- demand suitable for the user-facing API.
derefDemand :: ListDemand PrimDemand IORef
            -> IO (ListDemand PrimDemand Identity)
derefDemand demand = do
  case demand of
    Cons primRef listRef ->
      do primDemand <- coerce <$> readIORef primRef
         maybeListDemand <- readIORef listRef
         case maybeListDemand of
           Nothing -> return $ Cons (Identity primDemand) (Identity Nothing)
           Just listDemand -> do
             listDemand' <- derefDemand listDemand
             return $ Cons (Identity primDemand) (Identity (Just listDemand'))

-- Instrument lists to report their evaluation in a particular IORef

-- NOTE: instrumentListD relies on instrumentPrim -- this won't be caught by
-- the type-checker if you omit the call to instrumentPrim; you'll just never
-- see the results of primitives being evaluated. This demonstrates yet one
-- more justification for why generic programming is useful/necessary here.

{-# NOINLINE instrumentListD #-}
instrumentListD :: IORef (Maybe (ListDemand PrimDemand IORef)) -> [a] -> [a]
instrumentListD demand as =
  case as of
    [] -> []
    (a : as) ->
      unsafePerformIO $ do
        primDemand <- newIORef Nothing
        listDemand <- newIORef Nothing
        writeIORef demand $
          Just (Cons primDemand listDemand)
        return $ instrumentPrim primDemand a  -- NOTE: never forget this
               : instrumentListD listDemand as

{-# NOINLINE instrumentPrim #-}
instrumentPrim :: IORef (Maybe (PrimDemand IORef)) -> a -> a
instrumentPrim demand a =
  unsafePerformIO $ do
    writeIORef demand $ Just Demanded
    return a
