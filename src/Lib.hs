{-# LANGUAGE TemplateHaskell, OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
-- {-# LANGUAGE CPP #-}

module Lib where
import Language.Haskell.TH hiding (Name)
import Control.Applicative
import Turtle
import Data.List
import System.IO.Unsafe

import qualified Data.MemoCombinators as MC
import Data.RunMemo

import Control.Parallel
import Control.Parallel.Strategies

import Math.Combinat.Compositions

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Unsafe
import Control.Monad.Reader
import Control.Monad.Random
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

type Nm = Name Expr

data Expr
   = Var Nm
   | Lam (Bind Nm Expr)
   | App Expr Expr
   deriving (Show, Generic, Typeable, Eq)

instance (Typeable a, Alpha a, Eq a) => Eq (Bind (Name a) a) where
   (==) = aeq

instance Alpha Expr
instance Subst Expr Expr where
   isvar (Var x) = Just (SubstName x)
   isvar _       = Nothing

var = Var . s2n
lam x = Lam . bind x

_S = lam x . lam y . lam z $ App xz yz
   where
      x = s2n "x"
      y = s2n "y"
      z = s2n "z"
      xz = Var x `App` Var z
      yz = Var y `App` Var z
_K = lam x . lam y $ Var x
   where
      x = s2n "x"
      y = s2n "y"

beta (App (Lam b) e2) = do (x,e) <- unbind b
                           return $ subst x e2 e
beta _                = empty

redN intoLam e@(Var _) = pure e
redN intoLam e@(Lam b)
    | intoLam  = do (x,e1) <- unbind b
                    lam x <$> red e1
    | otherwise = pure e
    where
        red = redN intoLam
redN intoLam e@(App e1 e2)
    | isLam  e1  = beta e  >>= red
    | hasRed e1  = App <$> eval e1 <*> pure e2  >>= red
    | hasRed e2  = App <$> pure e1 <*> red  e2
    | otherwise  = pure e
    where
        eval = redN False
        red  = redN intoLam

reduceN = redN True

redP intoLam e@(Var _) = pure e
redP intoLam e@(Lam b)
    | intoLam  = do (x,e1) <- unbind b
                    lam x <$> red e1
    | otherwise = pure e
    where
        red = redP intoLam
redP intoLam e@(App e1@(App _ _) e2) =
    App <$> eval e1 <*> pure e2  >>= red
    where
        eval = redN False
        red  = redN intoLam
redP intoLam e@(App e1 e2)
    | isLam  e1  = beta e  >>= red
    | hasRed e1  = App <$> eval e1 <*> pure e2  >>= red
    | hasRed e2  = App <$> pure e1 <*> red  e2
    | otherwise  = pure e
    where
        eval = redN False
        red  = redN intoLam

reduceP = redP True

{-
redP intoLam e@(Var _) = pure e
redP intoLam e@(Lam b)
    | intoLam  = do (x,e1) <- unbind b
                    lam x <$> red e1
    | otherwise = pure e
    where
        red = redP intoLam
redP intoLam e@(App e1 e2) = App <$> eval e1 <*> red e2  >>= red'
   where
       red e    | hasRed e   = redP intoLam e
                | otherwise  = pure e
       eval e   | hasRed e   = redP False   e
                | otherwise  = pure e
       red' e'@(App e1' e2')
            | isLam  e1'  = beta e' >>= red
            | hasRed e1'  = App <$> red e1' <*> pure e2'
            | otherwise   = pure e'

reduceP = redP True
-}

isLam (Lam _) = True
isLam _       = False

hasRed (Var _)     = False
hasRed (Lam b)     = hasRed . snd $ unsafeUnbind b
hasRed (App e1 e2) = isLam e1 || hasRed e1 || hasRed e2


_nat n = lam f . lam x . foldr App _x $ replicate n _f
    where
        f = s2n "f";_f = Var f
        x = s2n "x";_x = Var x

_succ = lam n . lam f . lam x . App _f $ foldl1 App [_n,_f,_x] 
    where
        f = s2n "f";_f = Var f
        x = s2n "x";_x = Var x
        n = s2n "n";_n = Var n

_plus = lam m . lam n . lam f . lam x $ foldl1 App [ _m, _f, foldl1 App [_n,_f,_x] ]
    where
        f = s2n "f";_f = Var f
        x = s2n "x";_x = Var x
        n = s2n "n";_n = Var n
        m = s2n "m";_m = Var m

_mult = lam m . lam n . lam f . lam x $ foldl1 App [ _m,  App _n _f, _x ]
    where
        f = s2n "f";_f = Var f
        x = s2n "x";_x = Var x
        n = s2n "n";_n = Var n
        m = s2n "m";_m = Var m

_exp  = lam m . lam n $ App _n _m
    where
        n = s2n "n";_n = Var n
        m = s2n "m";_m = Var m

_pred = lam n . lam f . lam x $
            foldl1 App  [ _n
                        , lam g . lam h . App _h $ App _g _f
                        , lam u _x
                        , lam u _u
                        ]
    where
        f = s2n "f";_f = Var f
        x = s2n "x";_x = Var x
        g = s2n "g";_g = Var g
        h = s2n "h";_h = Var h
        u = s2n "u";_u = Var u
        n = s2n "n";_n = Var n

_minus = lam m . lam n $ foldl1 App [_n, _pred, _m]
    where
        n = s2n "n";_n = Var n
        m = s2n "m";_m = Var m

_true  = lam x . lam y $ _x
    where
        x = s2n "x";_x = Var x
        y = s2n "y";_y = Var y

_false = lam x . lam y $ _y
    where
        x = s2n "x";_x = Var x
        y = s2n "y";_y = Var y

_is0 = lam n $ foldl1 App [_n, lam x _false, _true]
    where
        x = s2n "x";_x = Var x
        n = s2n "n";_n = Var n

_Y = lam f $ App _f_xx _f_xx
    where
        _f_xx = lam x . App _f $ App _x _x
        x = s2n "x";_x = Var x
        f = s2n "f";_f = Var f


_fibo = App _Y $ lam f . lam n $
            foldl1 App  [ App _is0 _n_1
                        , _nat 1                                       -- when true
                        , foldl1 App [_plus, App _f _n_1, App _f _n_2] -- when false
                        ]
    where
        _n_1 = App _pred _n
        _n_2 = App _pred $ _n_1
        f = s2n "f";_f = Var f
        n = s2n "n";_n = Var n

{-
_s x y z = x z (y z)
_k x y = x

_ss = _s _s
_sk = _s _k
_ks = _k _s
_kk = _k _k
-- _ = _ss _s -- error
-- _ = _ss _k -- error
-- _ = _ss _sk

vS = var "s"
vK = var "k"

-- assuming only Var and App are used (i.e., no Lam)
e2s (Var x) = show x
e2s (App e1 e2@(App _ _)) = e2s e1 ++ " ("++ e2s e2 ++")"
e2s (App e1 e2)           = e2s e1 ++ " " ++ e2s e2

combs_ 0 = []
combs_ 1 = [vS,vK]
combs_ n
    | n < len   = combsList!!n
    | otherwise = filter (tychk . e2s) [foldl1 App (c:ts) | c<-[vS,vK], ns<-nss, ts<-mapM (combsList!!) ns]
    where
        len = length combsListBegin
        nss = reverse . concat $ allCompositions1 (n-1)

-- # include "CombsListBegin.txt"
combsListBegin = []

combsList = combsListBegin ++ map combs_ [n..]
    where n = length combsListBegin

combs = (combsList!!)

tychk src = (ExitSuccess ==) . unsafePerformIO $
    proc "runhaskell" empty $
        "s x y z = x z (y z)" <> ";" <>
        "k x y = x" <> ";" <>
        "_ = "<> fromString src <> ";" <>
        "main = return ()"

outputCombsListBegin n = output (fromString "src/CombsListBegin.txt")
    . fromString
    . ("combsListBegin = let (s,k)=(s2n\"s\",s2n\"k\") in "++)
    . show . runEval . parList rpar $ take n combsList
-}