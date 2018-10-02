{-# LANGUAGE GADTs #-}

module RefTrans where

import System.Exit
import System.IO

import Test.StrictCheck

notEqualRefTrans :: Eq a => String -> a -> a -> IO Bool
notEqualRefTrans functionName x y =
  if x /= y
  then return True
  else do
    putStrLn $ "!!! " ++ functionName ++ " referentially opaque"
    return False

checkRefTrans :: IO ()
checkRefTrans = do
  let strict = snd (observe1 id (\() -> ()) ())
  let lazy   = snd (observe1 id (\_  -> ()) ())

  observe1_ok <- notEqualRefTrans "observe1" strict lazy

  let strict' = snd (observeNP id (\(I () :* Nil) -> ()) (I () :* Nil))
  let lazy'   = snd (observeNP id (\(I _  :* Nil) -> ()) (I () :* Nil))

  observe_ok <- notEqualRefTrans "observe" strict' lazy'

  let strict'' = snd (observe id (\() -> ()) ())
  let lazy''   = snd (observe id (\_  -> ()) ())

  observeNP_ok <- notEqualRefTrans "observeNP" strict'' lazy''

  if and [observe1_ok, observe_ok, observeNP_ok]
    then return ()
    else putStrLn "\n" >> hFlush stdout >> exitFailure
