module TypeChgPlus where

import Monad
import NDSM
import TypeGU
import TypeGT

import Data.Generics


data FT = TVar MVar | TInt | TBool | Fun FT FT | Tup FT FT | Forall MVar FT | Undef | List FT
        deriving (Eq, Read, Typeable, Data)


newTVar = do
	m <- newMVar
	return (TVar m)

-- *** STUFF FOR SHOWING TYPES
perm [] = [[]]  
perm (x:xs) = [y:ys | y <- x, ys <- perm xs]


tvl n = perm (tvel n)
        where tvel 0 = []
              tvel n = [['a'..'z']]++ tvel (n-1)
tv = [x | n <- [1..], x <- tvl n]   

instance Show FT where
	show (TVar (MVar x)) = tv !! x
	show TInt = "Int"
	show TBool = "Bool"
	show Undef = "?"
	show (Fun s t) = showF s++"->"++show t
	show (Tup s t) = "("++show s++","++show t++")"
	show (Forall (MVar a) t) = "forall "++tv !! a++"."++show t
	show (List t) = "["++show t++"]"
showF t@(Fun _ _) = brack t
showF t           = show t
brack e = '(':show e++")"


	

instance Unifiable FT where

-- since we will be having expressions as a result
-- they must be subject to unification
data Expr = Var String | App Expr Expr | Lam String Expr | Pair Expr Expr
	| Let String Expr Expr | Chg Expr Expr | EVar MVar
        deriving (Eq, Read, Typeable, Data)

newEVar = do
	m <- newMVar
	return (EVar m)


instance Unifiable Expr where

instance Unifiable (Expr,FT) where

instance Isomorphic (Expr,FT) (Expr,FT) where
	to = id
	from = id

instance Isomorphic FT FT where
	to = id
	from = id

instance Wrapable FT where
	wrap = TVar


-- ** STUFF FOR SHOWING EXPRESSIONS
instance Show Expr where
  show (Var v)      = v   
  show (App f e)    = showL f++" "++showR e
  show (Lam v e)    = "\\"++v++"->"++show e
  show (Let v e' e) = "let "++v++"="++show e'++" in "++show e
  show (Pair e' e)   = "("++show e'++","++show e++")"
  show (Chg e e2) = "("++(show e)++" ~> " ++(show e2)++")"
  show (EVar (MVar t)) = "*"++(tv !! t)
showL e@(Lam _ _) = brack e
showL e           = show e
  
showR e@(Lam _ _) = brack e
showR e@(App _ _) = brack e
showR e           = show e



type Env = [(String, FT)]

instance Judgement (Env,Expr) (Expr,FT) where
	rules = [app, arg, par, var, tup, lam, letr, def]

app (env, (App e1 e2)) = do
		a <- newTVar
		b <- newTVar
		f <- newEVar
		g <- newEVar
		(env, e1) .>. (f, (Fun a b))
		(env, e2) .>. (g, a)
		return (App f g, b)
app _ = mzero

arg (env, (App e1 e2)) = do
		a <- newTVar
		b <- newTVar
		c <- newTVar
		f <- newEVar
		g <- newEVar
		(env, e1) .>. (f, (Fun a b))
		(env, e2) .>. (g, c)
		a ./=. c
		-- find all in env ==c
		(str,ft) <- extEnv env
		-- match the type of ft to a
		ft .==. a
		return (App f (Chg g (Var str)), b)
arg _ = mzero


par (env, (App e1 e2)) = do
		a <- newTVar
		b <- newTVar
		c <- newTVar
		f <- newEVar
		g <- newEVar
		(env, e1) .>. (f, (Fun a b))
		(env, e2) .>. (g, c)
		a ./=. c
		-- find all in env ==c
		(str,ft) <- extEnv env
		-- match the type of ft to a
		ft .==. (Fun c b)
		return (App (Chg f (Var str)) g, b)
par _ = mzero


var (env, va@(Var x)) = case (lookup x env) of
			(Just y) -> do
				y' <- forall' y
				return (va,y')
			Nothing -> do
				a <- newTVar
				-- find all in env ==c
				(str,ft) <- extEnv env
				-- match the type of ft to a
				ft .==. a
				return (Chg (Var x) (Var str), a)
var _ = mzero

vchg (env, (Var x)) = case (lookup x env) of
			(Just y) -> do
				a <- newTVar
				y' <- forall' y
				-- find all in env ==c
				(str,ft) <- extEnv env
				-- match the type of ft to a
				ft .==. a
				return (Chg (Var x) (Var str), a)
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
		-- find all in env ==c
		(str,ft) <- extEnv env
		-- match the type of ft to a
		ft .==. c
                return (Let x (Chg f (Var str)) g,b)
def _ = mzero


extEnv :: Env -> M (String, FT)
extEnv ((s,f):env) = do
	mplus (return (s,f)) (extEnv env)
extEnv [] = mzero

--(./=.) = bp ( (/=) :: FT -> FT -> Bool)

(./=.) x y = do
	a <- newTVar
	bind (GFS ((\[x, y]->
		case (gunify x y) of
		(Just _) -> mzero
		Nothing -> do {m <- newMVar; return (mkGS m);}) , [mkGS x, mkGS y])
		) a
	return a


-- generalize: for all variables v, prefix type with Forall v
gen :: FT -> FT
gen t = foldr Forall t (findvars t)

gen' = uf gen

findvars :: FT -> [MVar]
findvars (Fun x y) = (findvars x)++(findvars y)
findvars (Tup x y) = findvars (Fun x y)
findvars (TVar x) = [x]
findvars _ = []

-- forall: substitute new variables for all universally quantified
-- variables
forall :: FT -> M FT
forall (Forall t x) = do
	t' <- newTVar
	let x' = sub x (TVar t) t'
	forall x'
forall x = return x

forall' = ufM forall


-- EXAMPLES


set (expr,ty) = (show expr)++" :: "++(show ty)

minf x y = map set (inf (x,y))

uda = minf ([]::Env) (App (Var "x") (Var "y"))

nott = minf
	baseenv
	(App (Var "not") (Var "t"))

not1 = minf
	baseenv
	(App (Var "not") (Var "1"))


ptt = minf
	baseenv
	(App (App (Var "plus") (Var "t")) (Var "t"))
sid = minf 
	baseenv
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))

nsid = minf
	(("id", Fun (TVar (MVar 2)) (TVar (MVar 2))):baseenv)
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))

oknsid = minf
	(("id", Fun (TVar (MVar 2)) (TVar (MVar 2))):baseenv)
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "2")))


lxx = Lam "x" (Var "x")

letsid = minf [("t", TBool), ("1", TInt)]
	(Let "id" (Lam "x" (Var "x")) 
	(Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))
	)


cons x y = App (App (Var "cons") x) y

tough1 = (Lam "x" (Lam "y" (Pair (App (Var "y") (Var "x")) 
        (App (Var "x") (cons (Var "y") (Var "el"))))))

tough2 = (App (App (Var ".") (Var "not")) (Var "eq"))
        
tough3 = App (App (App (Var "foldl") (Var "cons")) 
        (App (App (Var "cons") i1) (Var "el")) ) 
        (App (App (Var "cons") i1) (Var "el"))

tough4 = Lam "folding" (App (Var "suc") (Var "fold"))

tough5 = Lam "n" (App (App (App (Var "foldl") (Var "succ")) i1) (Var "n"))


letx11 = minf baseenv
	(Let "x" (Var "1") (App (Var "x") (Var "x")))

plus x y       = App (App (Var "plus") x) y
if2 x y z       = App (App (App (Var "if") x) y) z
i1 = Var "1"
eq  x y        = App (App (Var "eq") x) y


fac1  = Let "fac" (Lam "n" (if2 (eq (Var "n") i1) i1 (plus (Var "n") (App (Var "fac")
                        (plus (Var "n") i1))))) (App (Var "fac") i1)

t = Var "t"

bernstein1995a  = Lam "f" (Lam "g" (Lam "a" (Pair
        (Pair (App (Var "f") (Var "a")) (App (Var "f") i1))
        (Pair (App (Var "g") (Var "a")) (App (Var "g") t))
        )))



choppella1995b = Lam "x" (if2 (Var "x") (App (Var "succ") (Var "x")) (Var "x"))

heeren2002a_a = App
        (Lam "x" (App (Var "succ") (Var "x")))
        (App (Lam "y" (if2 (Var "y") t t)) t)



a = TVar (MVar (-1))
b = TVar (MVar (-2))
c = TVar (MVar (-3))

baseenv = [("1", TInt), ("2", TInt), ("t", TBool),
        ("eq", Forall (MVar (-1)) (Fun a (Fun a TBool))),
        ("if", Forall (MVar (-1)) (Fun TBool (Fun a (Fun a a)))),
        ("plus", Fun TInt (Fun TInt TInt)),
        ("id", Forall (MVar (-1)) (Fun a a)),
	("not", Fun TBool TBool),
	("foldl", Forall (MVar (-2)) $ Forall (MVar (-1)) $ 
		Fun (Fun a (Fun b a)) (Fun a (Fun (List b) a))),
        ("map", Forall (MVar (-2)) $ Forall (MVar (-1)) $
		Fun (Fun a b) (Fun (List a) (List b))),
        (".", Forall (MVar (-3)) $ Forall (MVar (-2)) $ Forall (MVar (-1)) $ 
		Fun (Fun a b) (Fun (Fun c a) (Fun c b))),
        ("cons", Forall (MVar (-1)) (Fun a (Fun (List a) (List a)))),
	("el", Forall (MVar (-1)) $ List a),
	("succ", Fun TInt TInt)
	]

