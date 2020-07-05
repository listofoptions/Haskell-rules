module TypeChgMin where

import Monad
import TypeGT
import TypeChg


instance Judgement (Env,Expr) (Expr,FT) where
	rules = [app, var, tup, lam, letr, vchg]

app (env, (App e1 e2)) = do
		a <- newTVar
		b <- newTVar
		f <- newEVar
		g <- newEVar
		(env, e1) .>. (f, (Fun a b))
		(env, e2) .>. (g, a)
		return (App f g, b)
app _ = mzero

var (env, va@(Var x)) = case (lookup x env) of
			(Just y) -> do
				y' <- forall' y
				return (va,y')
			Nothing -> do
				a <- newTVar
				return (Chg (Var x) Undef a, a)
var _ = mzero

vchg (env, (Var x)) = case (lookup x env) of
			(Just y) -> do
				a <- newTVar
				y' <- forall' y
				-- a ./=. y'
				return (Chg (Var x) y' a, a)
			Nothing -> mzero
vchg _ = mzero

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
