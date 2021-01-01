{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Lib
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Stream ( Stream )
import Control.Monad.Random
import System.Random
import Control.Monad.State
import Control.Monad.Identity
import Control.Parallel
import Control.Parallel.Strategies
import Data.List ( partition, union, sort, nub, (\\) )
import Data.Tree ( Tree(Node) )
import qualified Data.MemoCombinators as MC
import Data.RunMemo
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Control.Monad.Reader
import Control.Monad.Random
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import qualified Control.Monad.Parallel as MP

expr1 = bind x (Var x)
   where x = s2n "x" :: Nm

parFreshM strat ms = do
   s <- FreshMT $ get
   return . runEval . parList strat $ map (`contFreshM` s) ms

-- parFreshM strat ms = fmap runIdentity <$> parFreshMT (parTraversable strat) ms

parFreshMT :: (Monad m1, Monad m2) => Strategy (m2 a) -> [FreshMT m2 a] -> FreshMT m1 [m2 a]
parFreshMT strat ms = do
   s <- FreshMT $ get
   return . runEval . parList strat $ map (`contFreshMT` s) ms

main :: IO ()
main = do
   let (b,es@[e1,e2]) = head . runFreshMT $ do
               e1 <- reduceN $ exprFibo 9
               e2 <- reduceP $ exprFibo 9
               return (e1==e2, [e1,e2])
   mapM_ print es
   print b

expr2 = foldl1 App [_minus, _nat 10, _nat 8]

exprFibo x = App _fibo (_nat x)

{-
roll n = sequence . replicate n

main = do
   main' 3
   return ()

228

main' n = do
   let g = mkStdGen 217
   let xs = roll n (getRandomR (0,9::Int)) `evalRand` g
   let e = appHalves n $ [if x>3 then _S else _K | x <- xs]
   let (b,es@[e1,e2]) = head . runFreshMT $ do
                  e1 <- reduceN e
                  e2 <- reduceP e
                  return (e1==e2, [e1,e2])
   mapM_ print es
   print n
   return b

appHalves 1 (e:_)= e
appHalves n es = appHalves n1 es1 `App` appHalves n2 es2
   where
      n1 = n `div` 2
      n2 = n - n1
      (es1,es2) = splitAt n1 es
-}

-- main =  print . filter (/=Nothing) =<< mapM evaluate ( take 500000 (toList $ pythaTrip' =<< number3) `using` parList rseq )
-- main = mapM_ evaluate ( take 11 (toList $ pythaTrip =<< number3) `using` parList rdeepseq )
-- main = example1
-- main = mapM_ evaluate (nqueens 13)
-- main = mapM_ evaluate (nqueens' 13)
-- main = mapM_ evaluate [bisimilar' systemPPPP systemPPPP]
{-
main = do
   g <- getStdGen
   let es = genTree 225 ["a","b"] `evalRand` g 
   let system = (0, es)
   print $ bisimilarM' system system
-}
   
   --   print $ example3 search

pythaTrip' :: (Int,Int,Int) -> Stream (Maybe (Int,Int,Int))
pythaTrip' (i,j,k) = 
     if sum [1..busyN] - sum [1..busyN] + i*i + j*j == k*k
        then return (Just (sum [1..busyN] - sum [1..busyN] +i,j,k))
        else return Nothing

pythaTrip :: (Int,Int,Int) -> Stream (Int,Int,Int)
pythaTrip (i,j,k) = do
     guard $ sum [1..busyN] - sum [1..busyN] + i*i + j*j == k*k
     return (sum [1..busyN] - sum [1..busyN] + i,j,k)

busyN = 10000000

number :: Stream Int
number = return 1 `mplus` (number >>= (return . (+1)))

number3 = do
   i <- number
   j <- number
   k <- number
   return (i,j,k)

pythagoreanTriples :: Stream (Maybe (Int,Int,Int))
pythagoreanTriples = do
     let number = return 1 `mplus` (number >>= (return . (+1)))
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

{-
example1 =
   do print =<< mapM evaluate (parMap rseq f [1..16]) -- ( map f [1..16] `using` parBuffer 4 rseq )
   where
      f x = last $ map (x*) [1..100000000]
-}

-- >>> takeTree 3 (mkTree "")
-- Node {rootLabel = "", subForest = [Node {rootLabel = "0", subForest = [Node {rootLabel = "00", subForest = []},Node {rootLabel = "10", subForest = []},Node {rootLabel = "20", subForest = []},Node {rootLabel = "30", subForest = []}]},Node {rootLabel = "1", subForest = [Node {rootLabel = "01", subForest = []},Node {rootLabel = "11", subForest = []},Node {rootLabel = "21", subForest = []},Node {rootLabel = "31", subForest = []}]},Node {rootLabel = "2", subForest = [Node {rootLabel = "02", subForest = []},Node {rootLabel = "12", subForest = []},Node {rootLabel = "22", subForest = []},Node {rootLabel = "32", subForest = []}]},Node {rootLabel = "3", subForest = [Node {rootLabel = "03", subForest = []},Node {rootLabel = "13", subForest = []},Node {rootLabel = "23", subForest = []},Node {rootLabel = "33", subForest = []}]}]}

nqueens :: Int -> [[Int]]
nqueens n = subtree n []
  where
  subtree 0 b = [b]
  subtree c b = concat (map (subtree (c-1)) (children b) `using` parList rseq)
  children b = [ q:b | q <- [1..n], safe q b ]
  safe q b = notElem q b && and [ abs(q-q') /= d | (d,q') <-zip [1..] b ]


nqueens' n = gen n
   where
   gen :: Int -> [[Int]]
   gen 0 = [[]]
   gen c = [ q:b | b <- gen (c-1), q <- [1..n], safe q b ] `using` parBuffer 4 rseq
   safe q b = notElem q b && and [ abs(q-q') /= d | (d,q') <-zip [1..] b ]


bisimilar sysP@(p0,esP) sysQ@(q0,esQ) = bisim p0 q0
  where
  bisim p q = and [or [bisim p1 q1 | (q',b,q1) <- esQ, q==q', a==b]
                                   | (p',a,p1) <- esP, p==p']
           && and [or [bisim p1 q1 | (p',a,p1) <- esP, p==p', b==a]
                                   | (q',b,q1) <- esQ, q==q']


bisimilar' sysP@(p0,esP) sysQ@(q0,esQ) = bisim p0 q0
  where
  bisim p q = and [or [bisim p1 q1 | (q',b,q1) <- esQ, q==q', a==b]
                                   | (p',a,p1) <- esP, p==p']
     `parAnd` and [or [bisim p1 q1 | (p',a,p1) <- esP, p==p', b==a]
                                   | (q',b,q1) <- esQ, q==q']

e1 `parAnd` e2 = e2 `par` (e1 && e2)


bisimilarM sysP@(p0,esP) sysQ@(q0,esQ) = runMemo mcIntPair bisim' (p0,q0)
  where
  bisim' bisim(p,q)
            = and [or [bisim(p1,q1)| (q',b,q1) <- esQ, q==q', a==b]
                                   | (p',a,p1) <- esP, p==p']
           && and [or [bisim(p1,q1)| (p',a,p1) <- esP, p==p', b==a]
                                   | (q',b,q1) <- esQ, q==q']

mcIntPair :: ((Int, Int) -> r) -> (Int, Int) -> r
mcIntPair = MC.pair MC.integral MC.integral


bisimilarM' sysP@(p0,esP) sysQ@(q0,esQ) = runMemo mcIntPair bisim' (p0,q0)
  where
  bisim' bisim(p,q)
            = and [or [bisim(p1,q1)| (q',b,q1) <- esQ, q==q', a==b]
                                   | (p',a,p1) <- esP, p==p']
     `parAnd` and [or [bisim(p1,q1)| (p',a,p1) <- esP, p==p', b==a]
                                   | (q',b,q1) <- esQ, q==q']



genSortedPairs n = do
   x <- getRandomR (0,n-1)
   y <- getRandomR (x+1,n)
   return (x,y) -- 0 <= x < y <= n

genLabel as (x,y) = do
   l <- fromList [(a,1) | a<-as]
   return (x,l,y)


genDAG :: (MonadRandom m) => Int -> [String] -> m [(Int, String, Int)]
genDAG n as = do 
   ps <- replicateM eSize (genSortedPairs n)
   mapM (genLabel as) (sort $ nub ps)
   where
      eSize = n^2 `div` 2


genTree n as = reachableFrom 0 <$> genDAG n as

reachableFrom v0 es = reachFrom [v0] es []

reachFrom xs es acc
   | null rs   = acc 
   | otherwise = reachFrom xs' es' (acc++rs)
   where
      xs' = [x' | (_,_,x')<-rs]
      (rs, es') = partition (\(x,_,_) -> x `elem` xs) es

-- esPPPP = [(0,"a",4),(0,"a",5),(0,"a",14),(0,"b",1),(0,"b",6),(0,"b",11),(0,"b",12),(0,"b",13),(1,"a",7),(1,"a",11),(1,"a",13),(1,"a",14),(1,"b",2),(1,"b",3),(1,"b",4),(1,"b",5),(1,"b",10),(2,"a",7),(2,"a",8),(2,"a",11),(2,"b",3),(2,"b",5),(2,"b",12),(2,"b",13),(3,"a",7),(3,"a",12),(3,"a",14),(3,"b",5),(3,"b",8),(4,"a",8),(4,"a",12),(4,"a",13),(4,"a",14),(4,"b",5),(5,"a",6),(5,"a",9),(5,"a",14),(5,"b",10),(5,"b",11),(6,"a",9),(6,"b",8),(6,"b",14),(7,"a",9),(7,"a",11),(7,"a",12),(7,"b",8),(7,"b",14),(8,"a",10),(8,"a",14),(8,"b",11),(8,"b",13),(9,"a",13),(9,"b",10),(9,"b",14),(10,"a",13),(10,"a",14),(10,"b",11),(11,"b",12),(11,"b",13),(11,"b",14),(12,"a",13),(12,"a",14),(13,"a",14)]
-- esPPPP = [(0,"a",9),(0,"b",1),(0,"b",3),(0,"b",6),(0,"b",13),(1,"a",2),(1,"a",6),(1,"a",7),(1,"a",15),(1,"b",8),(1,"b",9),(2,"a",8),(2,"b",4),(2,"b",6),(2,"b",7),(2,"b",14),(2,"b",15),(3,"a",4),(3,"b",5),(3,"b",8),(3,"b",15),(4,"a",5),(4,"a",7),(4,"a",10),(4,"b",8),(4,"b",9),(4,"b",14),(4,"b",15),(5,"a",7),(5,"a",14),(5,"b",9),(5,"b",11),(5,"b",15),(6,"a",12),(6,"a",13),(6,"a",14),(6,"a",15),(7,"a",8),(7,"a",9),(7,"a",12),(7,"b",10),(7,"b",13),(7,"b",14),(8,"a",9),(8,"a",13),(8,"a",15),(8,"b",10),(9,"a",11),(9,"a",12),(9,"a",13),(9,"a",15),(9,"b",10),(10,"a",11),(10,"b",12),(11,"a",12),(11,"a",13),(11,"b",14),(11,"b",15),(12,"a",13),(12,"a",14),(12,"a",15),(13,"a",14),(13,"b",15),(14,"a",15)]
esPPPP = [(0,"a",1),(0,"a",4),(0,"a",17),(0,"a",20),(0,"b",7),(0,"b",10),(0,"b",11),(0,"b",14),(0,"b",19),(1,"a",2),(1,"a",7),(1,"a",13),(1,"a",14),(1,"a",18),(1,"a",20),(1,"b",4),(1,"b",5),(1,"b",17),(1,"b",19),(2,"a",3),(2,"a",4),(2,"a",11),(2,"a",15),(2,"a",17),(2,"a",18),(2,"b",7),(2,"b",10),(2,"b",19),(2,"b",20),(3,"a",13),(3,"a",18),(3,"b",5),(3,"b",8),(3,"b",10),(3,"b",20),(4,"a",5),(4,"a",7),(4,"a",10),(4,"a",13),(4,"a",17),(4,"a",18),(4,"b",6),(4,"b",9),(4,"b",11),(4,"b",20),(5,"a",15),(5,"b",8),(5,"b",10),(5,"b",16),(5,"b",18),(5,"b",20),(6,"a",9),(6,"a",11),(6,"a",12),(6,"b",7),(6,"b",8),(6,"b",17),(6,"b",20),(7,"a",12),(7,"b",8),(7,"b",13),(7,"b",20),(8,"a",19),(8,"a",20),(8,"b",18),(9,"a",12),(9,"a",19),(9,"a",20),(9,"b",13),(9,"b",15),(9,"b",16),(10,"a",12),(10,"a",14),(10,"a",17),(10,"b",13),(10,"b",15),(10,"b",16),(10,"b",18),(10,"b",19),(11,"a",14),(11,"a",15),(11,"a",16),(11,"a",17),(11,"b",18),(11,"b",19),(12,"a",13),(12,"a",14),(12,"a",18),(12,"a",20),(12,"b",15),(12,"b",16),(12,"b",17),(12,"b",19),(13,"a",14),(13,"a",15),(13,"a",18),(13,"b",16),(13,"b",20),(14,"a",16),(14,"a",18),(15,"a",19),(15,"b",16),(15,"b",17),(15,"b",20),(16,"a",17),(16,"a",19),(16,"b",18),(16,"b",20),(17,"b",18),(17,"b",19),(17,"b",20),(18,"b",19),(18,"b",20),(19,"b",20)]

esQQQQ = [(0,"a",1),(0,"a",4),(0,"a",17),(0,"a",20),(0,"b",7),(0,"b",10),(0,"b",11),(0,"b",14),(0,"b",19),(1,"a",2),(1,"a",7),(1,"a",13),(1,"a",14),(1,"a",18),(1,"a",20),(1,"b",4),(1,"b",5),(1,"b",17),(1,"b",19),(2,"a",3),(2,"a",4),(2,"a",11),(2,"a",15),(2,"a",17),(2,"a",18),(2,"b",7),(2,"b",10),(2,"b",19),(2,"b",20),(3,"a",13),(3,"a",18),(3,"b",5),(3,"b",8),(3,"b",10),(3,"b",20),(4,"a",5),(4,"a",7),(4,"a",10),(4,"a",13),(4,"a",17),(4,"a",18),(4,"b",6),(4,"b",9),(4,"b",11),(4,"b",20),(5,"a",15),(5,"b",8),(5,"b",10),(5,"b",16),(5,"b",18),(5,"b",20),(6,"a",9),(6,"a",11),(6,"a",12),(6,"b",7),(6,"b",8),(6,"b",17),(6,"b",20),(7,"a",12),(7,"b",8),(7,"b",13),(7,"b",20),(8,"a",19),(8,"a",20),(8,"b",18),(9,"a",12),(9,"a",19),(9,"a",20),(9,"b",13),(9,"b",15),(9,"b",16),(10,"a",12),(10,"a",14),(10,"a",17),(10,"b",13),(10,"b",15),(10,"b",16),(10,"b",18),(10,"b",19),(11,"a",14),(11,"a",15),(11,"a",16),(11,"a",17),(11,"b",18),(11,"b",19),(12,"a",13),(12,"a",14),(12,"a",18),(12,"a",20),(12,"b",15),(12,"b",16),(12,"b",17),(12,"b",19),(13,"a",14),(13,"a",15),(13,"a",18),(13,"b",16),(13,"b",20),(14,"a",16),(14,"a",18),(15,"a",19),(15,"b",16),(15,"b",17),(15,"b",20),(16,"a",17),(16,"a",19),(16,"b",18),(16,"b",20),(17,"b",18),(17,"b",19),(17,"b",20),(18,"b",19),(18,"b",20)]


systemPPPP = (0,esPPPP)
systemQQQQ = (0,esQQQQ)
