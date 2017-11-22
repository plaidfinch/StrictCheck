
{-# LANGUAGE TypeApplications, TupleSections, DeriveAnyClass, DeriveGeneric #-}

module Continuations where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Cont
import Test.QuickCheck
import qualified Test.QuickCheck.Gen.Unsafe as Unsafe
import Data.Function
import Control.Spoon
import Data.List
import Control.Applicative
import Data.Foldable
import Data.Maybe
import Control.DeepSeq
import GHC.Generics

-- Playing around with continuations

m1, m2 :: (Integer -> ContT r IO Integer) -> Integer -> ContT r IO Integer

m1 _ 0 = return 0
m1 k i = do
  liftIO . putStrLn $ "i = " ++ show i
  j <- k (i - 1)
  liftIO . putStrLn $ show (i + j) ++ " = " ++ show i ++ " + " ++ show j
  return (i + j)

m2 _ 0 = return 1
m2 k i = do
  liftIO . putStrLn $ "i = " ++ show i
  j <- k (i - 1)
  liftIO . putStrLn $ show (i * j) ++ " = " ++ show i ++ " * " ++ show j
  return (i * j)


----------------------------------------------------------
-- Experiments in generating random functions over nats --
----------------------------------------------------------

data Nat = Z | S Nat deriving (Eq, Generic, NFData)

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
  signum n = 1

instance Show Nat where
  show = show . natNum

-- must produce exactly one constructor of output
natProduce :: Gen Nat -> Gen Nat
natProduce gen =
  frequency [ (1,) $ variant 1 $ return Z
            , (3,) $ variant 2 $ S <$> gen
            ]

-- must consume either zero or one constructors of input
natConsume :: (Gen Nat -> Gen Nat) -> Nat -> Gen Nat
natConsume produce nat =
  frequency [ (1,) $ variant 0 $ produce (natConsume produce nat)
            , (2,) $
                case nat of
                  Z      -> variant 1 $ fix produce
                  S nat' -> variant 2 $ produce (natConsume produce nat')
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

prettyRandomNatFunction :: IO ()
prettyRandomNatFunction = do
  f <- generate natFunction
  let inputs = genericTake (c + 1) nats
      c      = continuity f
  putStrLn $ "\n   Continuity: " ++ show c ++ "\n"
  putStrLn $ "  Input  |  Output"
  putStrLn $ "---------+----------"
  forM_ inputs $ \input ->
    putStrLn $ (if natNum input < c then "    " else " ~  ")
            ++ show input
            ++ replicate (5 - (length $ show input)) ' ' ++ "|    "
            ++ show (f input)
  putStrLn "    ⋮    |    ⋮\n"
