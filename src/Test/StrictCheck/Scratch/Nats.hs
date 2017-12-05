{-# OPTIONS_GHC -fno-warn-type-defaults -fno-warn-name-shadowing #-}

{-# LANGUAGE TypeApplications, TupleSections, DeriveAnyClass, DeriveGeneric #-}

module Test.StrictCheck.Scratch.Nats where

import Control.Monad
import Test.QuickCheck
import qualified Test.QuickCheck.Gen.Unsafe as Unsafe
import Data.Function
import Control.Spoon
import Data.List
import Data.Maybe
import Control.DeepSeq
import GHC.Generics
import Data.IORef
import System.IO.Unsafe as Unsafe

import Test.StrictCheck.Produce
import Test.StrictCheck.Consume

import Test.StrictCheck.Scratch.Observe

----------------------------------------------------------
-- Experiments in generating random functions over nats --
----------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Ord, Generic, NFData)

instance Arbitrary Nat where
  arbitrary = frequency [ (1,) $ return Z
                        , (2,) $ S <$> arbitrary ]

natNum :: Nat -> Integer
natNum Z = 0
natNum (S n) = succ (natNum n)

numNat :: Integer -> Nat
numNat n | n <= 0    = Z
         | otherwise = S (numNat (pred n))

instance Num Nat where
  fromInteger = numNat
  a + b = numNat $ natNum a + natNum b
  a - b = numNat $ natNum a - natNum b
  a * b = numNat $ natNum a * natNum b
  abs = id
  signum 0 = 0
  signum _ = 1

instance Show Nat where
  show = show . natNum

instance Enum Nat where
  fromEnum n = fromInteger $ natNum n
  toEnum i = numNat (toInteger i)

{-# NOINLINE instrumentNat #-}
instrumentNat :: IORef Integer -> Nat -> Nat
instrumentNat count n =
  unsafePerformIO $
    case n of
      Z    -> modifyIORef' count succ >> return Z
      S n' -> modifyIORef' count succ >> return (S $ instrumentNat count n')

{-# NOINLINE natFunctionDemand #-}
natFunctionDemand :: (Nat -> ()) -> (Nat -> Nat) -> Nat -> Integer
natFunctionDemand c f input =
  unsafePerformIO $ do
    count <- newIORef 0
    let result = f $ instrumentNat count input
    evaluate (c result)
    forced <- readIORef count
    return forced

nStrict :: Integer -> Nat -> ()
nStrict 0 _ = ()
nStrict i n =
  case n of
    Z -> ()
    S n' -> nStrict (pred i) n'

natDemands :: (Nat -> Nat) -> [[Integer]]
natDemands f =
  let c = continuity f in
  flip map [0..c] $ \input ->
    flip map [0..f (numNat input) + 1] $ \demand ->
      natFunctionDemand (nStrict (natNum demand)) f (numNat input)

natProduce :: Gen Nat -> Gen Nat
natProduce gen =
  frequency [ (2,) $ variant 0 $ gen
            , (1,) $ variant 1 $ return Z
            , (2,) $ variant 2 $ S <$> gen
            ]

-- must consume either zero or one constructors of input
natConsume :: (Gen Nat -> Gen Nat) -> Nat -> Gen Nat
natConsume produce nat =
  frequency [ (1,) $ variant 1 $ produce (natConsume produce nat)
            , (1,) $ variant 2 $
                case nat of
                  Z      -> variant 3 $ fix produce
                  S nat' -> variant 4 $ produce (natConsume produce nat')
            ]

natFunction :: Gen (Nat -> Nat)
natFunction = Unsafe.promote $ natConsume natProduce

nats, partialNats :: [Nat]
nats        = iterate S Z
partialNats = iterate S undefined

continuity :: (Nat -> Nat) -> Integer
continuity f =
  genericLength . takeWhile isNothing $
    map (spoon . f) partialNats

undefinedAt :: Integer -> Nat
undefinedAt 0 = undefined
undefinedAt n = S (undefinedAt (pred n))

-- TODO: This is absurdly inefficient in very easy-to-fix ways.
prettyNatFunction :: (Nat -> Nat) -> IO ()
prettyNatFunction f = do
  let inputs = genericTake (c + 1) nats
      c      = continuity f
      demands = natDemands f
      demandBehaviors =
        flip map demands $ \list ->
          map (uncurry subtract) $
            zip list (tail list)

  putStrLn $ "\n  Input  |  Output  |  Demand Behavior"
  putStrLn $ "---------+----------+-------------------"
  forM_ (zip inputs demandBehaviors) $ \(input, behavior) ->
    putStrLn $ "    "
            ++ show input
            ++ replicate (5 - (length $ show input)) ' ' ++ "|    "
            ++ show (f input)
            ++ replicate (6 - (length $ show (f input))) ' ' ++ "|  "
            ++ intercalate " " (map (\n -> if n == 0 then "~" else show n) behavior)
  putStrLn $ "    ⋮    |    ⋮     |  "
          ++ intercalate " " (replicate (length (last demandBehaviors)) "⋮") ++ "\n"

natFunctionAboveContinuity :: Integer -> Gen (Nat -> Nat)
natFunctionAboveContinuity n = do
  f <- natFunction
  if continuity f >= n
    then return f
    else natFunctionAboveContinuity n

prettyRandomNatFunction :: IO (Nat -> Nat)
prettyRandomNatFunction = do
  f <- generate natFunction
  prettyNatFunction f
  return f

halve :: Nat -> Nat
halve Z         = Z
halve (S Z)     = Z
halve (S (S n)) = S (halve n)

double :: Nat -> Nat
double Z     = Z
double (S n) = S (S (double n))

isEven :: Nat -> Bool
isEven n | n == double (halve n) = True
         | otherwise             = False

minNat :: Nat -> Nat -> Nat
minNat    Z     _  = Z
minNat    _     Z  = Z
minNat (S m) (S n) = S (minNat m n)

-- Using Generate.hs
instance Produce Nat where
  produce inputs = do
    frequency [ (1, return Z)
              , (2, S <$> recur inputs)
              ]

instance Consume Nat
