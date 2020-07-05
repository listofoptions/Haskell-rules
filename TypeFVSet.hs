{-#LANGUAGE DeriveDataTypeable#-}
{-#LANGUAGE MultiParamTypeClasses#-}
{-#LANGUAGE FunctionalDependencies#-}
{-#LANGUAGE FlexibleInstances#-}
module TypeFVSet where

import TypeGU
import TypeGT

import Data.Generics
import Control.Monad

import Data.List 

data Expr = Var String | App Expr Expr | Lam String Expr
        deriving Show


--data VList a = VVar MVar | VCons a (VList a) | VEL
--  deriving (Eq, Read, Show, Typeable, Data)


--instance Isomorphic [a] (VList a) where
--  from (VCons x y) = x:(from y)
--  from VEL = []
--  to (x:xs) = (VCons x (to xs))
--  to [] = VEL


--instance Wrapable (VList a) where
--  wrap = VVar

instance Isomorphic [a] (L [a]) where
    to = V
    from (V x) = x

--instance Show (L [String]) where
--  show (V x) = show x

(.++.) = bf (++)
(.\\.) = bf (\\)
nub' = uf nub

instance Unifiable (L [String]) where

instance Judgement Expr (L [String]) where
    rules = [var, app, lam]

    

var (Var x) = return (to [x])
var _ = mzero

app (App e1 e2) = do
    a <- newVar
    b <- newVar
    e1 .>. a
    e2 .>. b
    (a .++. b) >>= nub' 
app _ = mzero

lam (Lam x e) = do
    a <- newVar
    e .>. a
    c <- (a .\\. (to [x]))
    return c
lam _ = mzero


-- EXAMPLES

vx = inf (Var "x")
        
vlx = inf (Lam "x" (Var "x"))

va = inf (App (Lam "x" (Var "x")) (Var "x"))
        
vay = inf (App (Lam "x" (Var "x")) (Var "y"))

vxy = inf (App (Var "x") (Var "y"))

vxx = inf (App (Var "x") (Var "x"))


