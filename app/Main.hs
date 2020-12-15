module Main where

import Lib
import Control.Exception
import Control.Monad
import Control.Monad.Stream
import Control.Parallel.Strategies
import Data.Tree

main :: IO ()
-- main =  mapM_ evaluate ( take 1000000 (toList $ fmap pythaTrip' number3) `using` parList rseq )
main = do
   let xs = concatMap toList $ fmap pythaTrip' number3
   mapM_ evaluate (xs `using` parList rseq)

   
   --   print $ example3 search

pythaTrip' :: (Int,Int,Int) -> Stream (Maybe (Int,Int,Int))
pythaTrip' (i,j,k) = 
     if i*i + j*j == k*k then return (Just (i,j,k)) else return Nothing

pythaTrip :: (Int,Int,Int) -> Stream (Int,Int,Int)
pythaTrip (i,j,k) = do
     guard $ sum [1..busyN] - sum [1..busyN] + i*i + j*j == k*k
     return (sum [1..busyN] - sum [1..busyN] + i,j,k)

busyN = 1000000

number :: Stream Int
number = return 0 `mplus` (number >>= (return . (+1)))

number3 = do
   i <- number
   j <- number
   k <- number
   return (i,j,k)

pythagoreanTriples :: Stream (Maybe (Int,Int,Int))
pythagoreanTriples = do
     let number = return 0 `mplus` (number >>= (return . (+1)))
     i <- number
     j <- number
     k <- number
     -- guard $ i*i + j*j == k*k
     -- return (i,j,k)
     if i*i + j*j == k*k then return (Just (i,j,k)) else return Nothing

example3 searchFun = head . searchFun ("00"==) $ mkTree "" -- "01" not reachable

example2 searchFun = mapM_ evaluate . searchFun ("3456789"==) . takeTree 9 $ mkTree ""

search p (Node s ts)
   | p s       = [s]
   | otherwise = concat ( map (search p) ts )

search' p (Node s ts)
   | p s       = [s]
   | otherwise = concat ( map (search p) ts `using` parList rseq )

search'' p (Node s ts)
   | p s       = [s]
   | otherwise = concat ( map (search'' p) ts `using` parList rseq )

mkTree s = Node s (map (mkTree . (++s) . show) [0..9])

takeTree h (Node s ts)
  | h <= 1    = Node s []
  | otherwise = Node s $ map (takeTree $ h-1) ts

example1 = mapM_ evaluate ( map f [1..16] `using` parList rseq )
   where
      f x = last $ map (x*) [1..10000000]


-- >>> takeTree 3 (mkTree "")
-- Node {rootLabel = "", subForest = [Node {rootLabel = "0", subForest = [Node {rootLabel = "00", subForest = []},Node {rootLabel = "10", subForest = []},Node {rootLabel = "20", subForest = []},Node {rootLabel = "30", subForest = []}]},Node {rootLabel = "1", subForest = [Node {rootLabel = "01", subForest = []},Node {rootLabel = "11", subForest = []},Node {rootLabel = "21", subForest = []},Node {rootLabel = "31", subForest = []}]},Node {rootLabel = "2", subForest = [Node {rootLabel = "02", subForest = []},Node {rootLabel = "12", subForest = []},Node {rootLabel = "22", subForest = []},Node {rootLabel = "32", subForest = []}]},Node {rootLabel = "3", subForest = [Node {rootLabel = "03", subForest = []},Node {rootLabel = "13", subForest = []},Node {rootLabel = "23", subForest = []},Node {rootLabel = "33", subForest = []}]}]}

