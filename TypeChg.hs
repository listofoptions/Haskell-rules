{-#LANGUAGE DeriveDataTypeable#-}
{-#LANGUAGE MultiParamTypeClasses#-}
{-#LANGUAGE FunctionalDependencies#-}
{-#LANGUAGE FlexibleInstances#-}
{-#LANGUAGE FlexibleContexts#-}
module TypeChg where

import Control.Monad
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
    | Let String Expr Expr | Chg Expr FT FT | EVar MVar
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

instance Wrapable Expr where
    wrap = EVar


-- ** STUFF FOR SHOWING EXPRESSIONS
instance Show Expr where
  show (Var v)      = v   
  show (App f e)    = showL f++" "++showR e
  show (Lam v e)    = "\\"++v++"->"++show e
  show (Let v e' e) = "let "++v++"="++show e'++" in "++show e
  show (Pair e' e)   = "("++show e'++","++show e++")"
  show (Chg e t1 t2) = "("++(show e)++" :: "++(show t1)++" ~> " ++(show t2)++")"
  show (EVar (MVar t)) = "*"++(tv !! t)
showL e@(Lam _ _) = brack e
showL e           = show e
  
showR e@(Lam _ _) = brack e
showR e@(App _ _) = brack e
showR e           = show e



type Env = [(String, FT)]




--(./=.) = bp ( (/=) :: FT -> FT -> Bool)

(./=.) x y = do
    a <- newTVar
    bind (GFS ((\[x, y]->
        case (gunify x y) of
        (Just _) -> mzero
        Nothing -> do {m <- newMVar; return (mkGS m);}) 
        , [mkGS x, mkGS y])
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


set ((expr,ty),cnt) = (show expr)++" :: "++(show ty)++" ("++show cnt++")"

--set (expr,ty) = (show expr)++" :: "++(show ty)

minf x y = map set (inf (x,y))

{--
uda = minf ([]::Env) (App (Var "x") (Var "y"))

nott = minf
    baseenv
    (App (Var "not") (Var "t"))

not1 = minf
    baseenv
    (App (Var "not") (Var "1"))


sid = minf 
    baseenv
    (Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))

nsid = minf
    (("id", Fun (TVar (MVar 2)) (TVar (MVar 2))):baseenv)
    (Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))

oknsid = minf
    (("id", Fun (TVar (MVar 2)) (TVar (MVar 2))):baseenv)
    (Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "2")))



letsid = minf [("t", TBool), ("1", TInt)]
    (Let "id" (Lam "x" (Var "x")) 
    (Pair (App (Var "id") (Var "1")) (App (Var "id") (Var "t")))
    )

--}

lxx = Lam "x" (Var "x")


cons x y = App (App (Var "cons") x) y

tough1 = (Lam "x" (Lam "y" (Pair (App (Var "y") (Var "x")) 
        (App (Var "x") (cons (Var "y") (Var "el"))))))

tough2 = (App (App (Var ".") (Var "not")) (Var "eq"))
        
tough3 = App (App (App (Var "foldl") (Var "cons")) 
        (App (App (Var "cons") i1) (Var "el")) ) 
        (App (App (Var "cons") i1) (Var "el"))

tough4 = Lam "folding" (App (Var "suc") (Var "fold"))

tough5 = Lam "n" (App (App (App (Var "foldl") (Var "succ")) i1) (Var "n"))

size15 = Pair choppella1995b tough4

size10 = Pair tough4 tough2
size10app = App tough4 tough2

size = App tough4 tough2 

deep f 0 = Var "x"
deep f n = f (deep f (n-1)) (deep f (n-1))

da2 = App (App (Var "foldl") (Var "succ")) (App (Var "map") (Var "plus"))

da2b = App (App (Var "succ") (Var "1")) (App (Var "map") (Var "map"))

lt = Lam "a" $ Lam "b" $ Lam "c" $ Lam "d" $ Lam "e" $ (deep App 2)


suc x = App (Var "succ") x

nt x = App (Var "not") x

ss = suc $ suc $ suc $ suc $ suc $ i1

ssr = suc $ suc $ suc $ suc $ nt $ i1

ssm = suc $ suc $ nt $ suc $ suc $ i1

ssl = nt $ suc $ suc $ suc $ nt $ i1

sx = suc (Var "x")

p x = Pair x x

sp1 = Pair (p (p (suc i1))) (p (suc i1))

sp2 = Pair (p (suc $ suc i1)) (suc $ suc i1)

sp3 = p (suc $ suc $ suc i1)

ssp1 = Pair (p (p (suc (Var "succ")))) (p (suc (Var "succ")))

ssp2 = Pair (p (suc $ suc (Var "succ"))) (p (suc (Var "succ")))

ssp3 = p (suc $ suc $ suc (Var "succ"))

tuple :: Int -> Int -> Expr -> Expr -> Expr
tuple k 1 x x' = if (k < 1) then x' else x
tuple k n x x' | odd n = Pair (tuple k 1 x x') (tuple (k-1) (n-1) x x') 
tuple k n x x' | even n = Pair (tuple k n2 x x') (tuple (k-n2) n2 x x')
    where n2 = n `div` 2

bapp :: Bool -> Int -> Int -> Expr -> Expr -> Expr -> Expr
bapp True k 1 _ _  x = x
bapp _ k 1 f f' x = if (k < 1) then f' else f
bapp b k n f f' x = App (bapp False k 1 f f' x) (bapp b (k-1) (n-1) f f' x) 


myt = [tuple 5 n (Var "succ") undefined | n <- [1..5]] ++
    [Lam "f" $ tuple 5 n (Var "f") undefined | n <- [1..5]] ++
    [tuple 5 n (App (Var "succ") i1) undefined | n <- [1..5]] ++
    [Lam "f" $ tuple k n (App (Var "succ") i1) (App (Var "f") i1) |
        n <- [1..5], k <- [0..5]]++
    [Lam "x" $ tuple k n (App (Var "succ") (Var "x")) (App (Var "succ") i1) |
        n <- [1..5], k <- [0..5]]++
    [bapp True 5 n (Var "succ") undefined i1 | n <- [1..5]]++
    [Lam "f" $ bapp True k n (Var "succ") (Var "f") i1 |
        n <- [1..5], k <- [0..5]]
    
fs = [mkf "f" "f" "f", mkf "f" "f" "g", mkf "f" "g" "h"]

fs2 = [mkf2 "f" "f" "f" "f", mkf2 "f" "f" "f" "g", mkf2 "f" "f" "g" "h",
    mkf2 "f" "g" "h" "a", mkf2 "f" "f" "g" "f", mkf2 "f" "g" "f" "f",
    mkf2 "g" "f" "f" "f"]

mkf x y z = Lam "f" $ Lam "g" $ Lam "h" $ App (Var x) (App (Var y) (App (Var z) i1))

mkf2 x y z a = Lam "f" $ Lam "g" $ Lam "h" $ Lam "a" $ App (Var x) (App (Var y) (App (Var z) (App (Var a) i1)))



vr1l = Let "x" i1 (Pair sx sx)

vr1' = App vr' i1

vr' = Lam "x" $ Pair sx sx

vr = Lam "x" $ Pair (Pair sx sx) (Pair sx sx)

vry = Lam "y" $ Pair (Pair sx sx) (Pair sx sx)


vrs = Lam "x" $ Lam "y" $ Lam "z" $ Lam "a" $ Pair 
    (Pair (suc (Var "x")) (suc (Var "y"))) 
    (Pair (suc (Var "z")) (suc (Var "a")))


vrs2 = Lam "x" $ Lam "y" $ Lam "z" $ Lam "a" $ Pair 
    (Pair (suc (Var "x")) (suc (Var "y"))) 
    (Pair (suc (Var "z")) (App (Var "not") (Var "x")))





--letx11 = minf baseenv -- (Let "x" (Var "1") (App (Var "x") (Var "x")))

plus x y       = App (App (Var "plus") x) y
if2 x y z       = App (App (App (Var "if") x) y) z
i1 = Var "1"
eq  x y        = App (App (Var "eq") x) y

t = Var "t"

fac1  = Let "fac" (Lam "n" (if2 (eq (Var "n") i1) i1 (plus (Var "n") (App (Var "fac")
                        (plus (Var "n") i1))))) (App (Var "fac") i1)

bernstein1995a  = Lam "f" (Lam "g" (Lam "a" (Pair
        (Pair (App (Var "f") (Var "a")) (App (Var "f") i1))
        (Pair (App (Var "g") (Var "a")) (App (Var "g") t))
        )))



choppella1995b = Lam "x" (if2 (Var "x") (App (Var "succ") (Var "x")) (Var "x"))

heeren2002a_a = App
        (Lam "x" (App (Var "succ") (Var "x")))
        (App (Lam "y" (if2 (Var "y") t t)) t)


h1 = (Lam "x" (App (Var "succ") (Var "x")))

h2 = (App (Lam "y" (if2 (Var "y") t t)) t)


a = TVar (MVar (-1))
b = TVar (MVar (-2))
c = TVar (MVar (-3))

baseenv = [("1", TInt), ("2", TInt), ("t", TBool),
        ("eq", Forall (MVar (-1)) (Fun a (Fun a TBool))),
        ("if", Forall (MVar (-1)) (Fun TBool (Fun a a))),
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


count :: String -> Expr -> Int
count x (App e1 e2) = (count x e1)+(count x e2)
count x (Pair e1 e2) = (count x e1)+(count x e2)
count x (Lam y e2) | y /= x = (count x e2)
count x (Let y e1 e2) | y /= x = (count x e1)+(count x e2)
count x (Var y) | y == x = 1
count _ _ = 0

profile :: Expr -> (Int,Int)
profile (App e1 e2) = (a1+a2+1,b1+b2)
    where  
        (a1,b1) = profile e1
        (a2,b2) = profile e1
profile (Pair e1 e2) = (a1+a2,b1+b2+1)
    where  
        (a1,b1) = profile e1
        (a2,b2) = profile e1
profile (Let _ e1 e2) = (a1+a2,b1+b2)
    where  
        (a1,b1) = profile e1
        (a2,b2) = profile e1
profile (Lam _ e1) = profile e1
profile _ = (0,0)

dvu :: [String] -> Expr -> (Int,Int)
dvu env (Var x) = case (elem x env) of
        True -> (1,0)
        False -> (0,1)
dvu env (App e1 e2) = (a1+a2,b1+b2)
    where  
        (a1,b1) = dvu env e1
        (a2,b2) = dvu env e2
dvu env (Lam x e1) = (a+count x e1,b)
    where  (a,b) = dvu (x:env) e1
dvu env (Pair e1 e2) = (a1+a2,b1+b2)
    where  
        (a1,b1) = dvu env e1
        (a2,b2) = dvu env e2
dvu env (Let x e1 e2) = (a1+a2,b1+b2)
    where  
        (a1,b1) = dvu (x:env) e1
        (a2,b2) = dvu (x:env) e2


dpa :: Expr -> Int
dpa (App e1 e2) = 1+(max a1 a2)
    where  
        a1 = dpa e1
        a2 = dpa e2
dpa (Lam x e1) = dpa e1
dpa (Pair e1 e2) = max a1 a2
    where  
        a1 = dpa e1
        a2 = dpa e2
dpa (Let x e1 e2) = max a1 a2
    where  
        a1 = dpa e1
        a2 = dpa e2
dpa _ = 0

allexs = [tough1, tough2, tough4, tough5, bernstein1995a, choppella1995b,
    size15, size10, size10app, deep Pair 5, deep Pair 3, deep App 2,
    deep App 3, da2, da2b, lt, ss, ssr, ssm, ssl, vr, vrs, vry,
    vr', vr1', vr1l, h1, h2]

ent :: Expr -> Int
ent (App e1 e2) = a1+a2
    where  
        a1 = ent e1
        a2 = ent e2
ent (Lam x e1) = (product [1..count x e1])+ent e1
ent (Pair e1 e2) = a1+a2
    where  
        a1 = ent e1
        a2 = ent e2
ent (Let x e1 e2) = a1+a2
    where  
        a1 = ent e1
        a2 = ent e2
ent _ = 0


ent2 :: Expr -> Int
ent2 (App e1 e2) = a1+a2
    where  
        a1 = ent2 e1
        a2 = ent2 e2
ent2 (Lam x e1) = if c > 1 then (2 ^ (c - 1))+ent e1 else ent e1
    where c = count x e1
ent2 (Pair e1 e2) = a1+a2
    where  
        a1 = ent2 e1
        a2 = ent2 e2
ent2 (Let x e1 e2) = a1+a2
    where  
        a1 = ent2 e1
        a2 = ent2 e2
ent2 _ = 0


