module Lib where

import Control.Monad.Random

someFunc :: IO ()
someFunc = putStrLn "someFunc"

die :: (RandomGen g) => Rand g Int
die = getRandomR (1,6)

dice :: (RandomGen g) => Int -> Rand g [Int]
dice n = sequence (replicate n die)