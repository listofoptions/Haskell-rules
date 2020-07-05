{-#LANGUAGE DeriveDataTypeable#-}
{-#LANGUAGE MultiParamTypeClasses#-}
{-#LANGUAGE FunctionalDependencies#-}
{-#LANGUAGE FlexibleInstances#-}
{-#LANGUAGE FlexibleContexts#-}
module Examples.TypeChgTrad where

import Control.Monad
import TypeGT
import Examples.TypeChg

instance Judgement (Env,Expr) (Expr,FT) where
    rules = [app, var, tup, lam, letr, arg, par, def]

app (env, (App e1 e2)) = do
        ~[a,b] <- newVars 2
        ~[f,g] <- newVars 2
        (env, e1) .>. (f, (Fun a b))
        (env, e2) .>. (g, a)
        return (App f g, b)
app _ = mzero

arg (env, (App e1 e2)) = do
        ~[a,b,c] <- newVars 3
        ~[f,g] <- newVars 2
        (env, e1) .>. (f, (Fun a b))
        (env, e2) .>. (g, c)
        a ./=. c
        return (App f (Chg g c a), b)
arg _ = mzero


par (env, (App e1 e2)) = do
        ~[a,b,c] <- newVars 3
        ~[f,g] <- newVars 2
        (env, e1) .>. (f, (Fun a b))
        (env, e2) .>. (g, c)
        a ./=. c
        return (App (Chg f (Fun a b) (Fun c b)) g, b)
par _ = mzero


var (env, va@(Var x)) = case (lookup x env) of
            (Just y) -> do
                y' <- forall' y
                return (va,y')
            Nothing -> do
                a <- newVar
                return (Chg (Var x) Undef a, a)
var _ = mzero

tup (env, (Pair e1 e2)) = do
        a <- newTVar
        b <- newTVar
        f <- newEVar
        g <- newEVar
        (env, e1) .>. (f, a)
        (env, e2) .>. (g, b)
        return (Pair f g, Tup a b)
tup _ = mzero

lam (env, (Lam x e)) = do
        a <- newTVar
        b <- newTVar
        f <- newEVar
        ((x,a):env, e) .>. (f, b)
        return (Lam x f, Fun a b)
lam _ = mzero

letr (env, (Let x e1 e2)) = do
        a <- newTVar
        b <- newTVar
        f <- newEVar
        g <- newEVar
        ((x,a):env, e1) .>. (f, a)
        m <- gen' a
        (((x, m):env), e2) .>. (g, b)
        return (Let x f g, b)
letr _ = mzero

def (env, (Let x e1 e2)) = do
        a <- newTVar
        b <- newTVar
        c <- newTVar
        f <- newEVar
        g <- newEVar
        ((x,a):env, e1) .>. (f, c)
        m <- gen' a
        (((x, m):env), e2) .>. (f, b)
        a ./=. c
        return (Let x (Chg f a c) g,b)
def _ = mzero
