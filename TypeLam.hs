module TypeLam where

import Monad
import NDSM
import List
import TypeGU
import TypeGT

import Data.Generics

data FT = TVar MVar | TInt | TBool | Fun FT FT | Tup FT FT | Forall MVar FT
        deriving (Eq, Show, Read, Typeable, Data)

instance Unifiable FT where

instance Isomorphic FT FT where
	from = id
	to = id

instance Wrapable FT where
	wrap = TVar

data Expr = Var String | App Expr Expr | Lam String Expr | Pair Expr Expr
	| Let String Expr Expr
        deriving (Eq,Show)

type Env = [(String, FT)]

instance Judgement (Env,Expr) FT where
	rules = [app, var, tup, lam, letr]


app (env, (App e1 e2)) = do
		[a,b] <- newVars 2
		(env, e1) .>. (Fun a b)
		(env, e2) .>. a
		return b
app x = mzero

var (env, (Var x)) = case (lookup x env) of
			(Just y) -> forall' y
			Nothing -> mzero
var x = mzero

tup (env, (Pair e1 e2)) = do
		a <- newVar
		b <- newVar
		(env, e1) .>. a
		(env, e2) .>. b
		return (Tup a b)
tup x = mzero

lam (env, (Lam x e)) = do
		a <- newVar
		b <- newVar
		((x,a):env, e) .>. b
		return (Fun a b)
lam x = mzero

letr (env, (Let x e1 e2)) = do
		a <- newVar
		b <- newVar
		((x,a):env, e1) .>. a
		c <- (gen' env a)
		(((x, c):env), e2) .>. b
		return b
letr x = mzero


-- generalize: for all variables v, prefix type with Forall v
gen :: Env -> FT -> FT
gen env t = foldr Forall t (fvt \\ fve)
	where	fvt = nub $ findvars t
		fve = nub $ concatMap (findvars.snd) env

gen' e = uf (gen e)

findvars :: FT -> [MVar]
findvars (Fun x y) = (findvars x)++(findvars y)
findvars (Tup x y) = findvars (Fun x y)
findvars (TVar x) = [x]
findvars _ = []


-- forall: substitute new variables for all universally quantified
-- variables
forall :: FT -> M FT
forall (Forall t x) = do
	t' <- newVar
	let x' = sub x (TVar t) t'
	forall x'
forall x = return x

forall' = ufM forall

-- EXAMPLES


set x ty = (show x)++" :: "++(show ty)

minf x y = map (set y) (inf (x,y))

sid = minf 
	baseenv
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))

nsid = minf
	(("id", Fun (TVar (MVar 1)) (TVar (MVar 1))):baseenv)
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))

oknsid = minf
	(("id", Fun (TVar (MVar 1)) (TVar (MVar 1))):baseenv)
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "2")))


lxx = Lam "x" (Var "x")

letsid = minf [("1", TInt), ("t", TBool)]
	(Let "id" (Lam "x" (Var "x")) 
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))
	)


plus x y       = App (App (Var "plus") x) y
if2 x y z       = App (App (App (Var "if") x) y) z
i1 = Var "1"
eq  x y        = App (App (Var "eq") x) y
aid x = App (Var "id") x

poly =  minf baseenv (Pair (aid (Var "t")) (aid i1))

fac1  = Let "fac" (Lam "n" (if2 (eq (Var "n") i1) i1 (plus (Var "n") (App 
			(Var "fac")
                        (plus (Var "n") i1))))) (App (Var "fac") i1)


baseenv = [("1", TInt), ("2", TInt), ("t", TBool), 
	("eq", Forall (MVar (-1)) (Fun (TVar (MVar (-1))) (Fun (TVar (MVar (-1))) TBool))),
	("if", Forall (MVar (-1)) (Fun TBool (Fun (TVar (MVar (-1))) (Fun (TVar (MVar (-1))) (TVar (MVar (-1))))))),
	("plus", Fun TInt (Fun TInt TInt)),
	("id", Forall (MVar (-1)) (Fun (TVar (MVar (-1))) (TVar (MVar (-1)))))]


-- interesting strucural change: x - 1 vs x (-1)

