{-#LANGUAGE DeriveDataTypeable#-}
{-#LANGUAGE MultiParamTypeClasses#-}
{-#LANGUAGE FunctionalDependencies#-}
{-#LANGUAGE FlexibleInstances#-}
{-#LANGUAGE FlexibleContexts#-}
module Examples.TypeFV where

import TypeGU
import TypeGT

import Data.Generics
import Control.Monad

data Expr = Var String | App Expr Expr | Lam String Expr
    deriving Show

data Free = Free
    deriving (Eq, Read, Show, Typeable, Data)

instance Unifiable Free where


instance Judgement (String, Expr) Free where
    rules = [var, app1, app2, lam]

var (v, (Var x)) | x == v = return Free
var _ = mzero

app1 (v, (App e1 e2)) = do
    (v, e1) .>. Free
    return Free
app1 _ = mzero

app2 (v, (App e1 e2)) = do
    (v, e2) .>. Free
    return Free
app2 _ = mzero

lam (v, (Lam x e)) = do
    (v, e) .>. Free
    if v == x then mzero else return Free
lam _ = mzero


-- Examples

vx = inf ("x", (Var "x"))

vlx = inf ("x", Lam "x" (Var "x"))

vy = inf ("y", (Var "x"))

va = inf ("x", App (Lam "x" (Var "x")) (Var "x"))

vay = inf ("x", App (Lam "x" (Var "x")) (Var "y"))

