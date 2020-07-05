-- ** GENERIC TYPING

module TypeGT where

import Maybe
import Monad
import TypeGU
import NDSM

import Foreign

import Data.Generics


-- use same type vars to sepcify input and output
-- m a b => M o b (o for output)
-- type synonym for M o o


newtype GFS = GFS ([GS] -> M GS, [GS])

type M b = NDSM (MVar, [(GS,GS)], [(GS, GFS)], Int) b

type R o = M o

newMVar :: M MVar
newMVar = NDSM (\(i,x,z,cnt)->[((succ i,x,z,cnt),succ i)])

class Wrapable o where
	wrap :: MVar -> o

newVar :: Wrapable o => M o
newVar = do
	a <- newMVar
	return (wrap a)

newVars :: Wrapable o => Int -> M [o]
newVars 1 = do
	a <- newVar
	return [a]
newVars cnt = do
	a <- newMVar
	rst <- newVars (cnt-1)
	return $ (wrap a):rst



merge :: [(GS,GS)] -> M ()
merge nx = NDSM (\(i,x,z,cnt)->case (gbiasl nx x) of
		(Just y) -> [((i, y, z, cnt), ())]
		Nothing -> mzero )

addFunc :: (GS, GFS) -> M ()
addFunc nx = NDSM (\(i, x, z, cnt)->[((i, x, nx:z, cnt), ())])

-- i: Structure to be analyzed (usually environment and expressions)
-- o: Structure produced by rules (usually types)

-- result should be entirely captured in b
class Unifiable o => 
	Judgement i o | i -> o  where
	rules :: [i -> R o]



bind :: Unifiable o => GFS -> o -> M ()
bind gfs typ = do
	let typ' = mkGS typ
	addFunc (typ', gfs)

bind_ :: GFS -> M ()
bind_ gfs = do
	typ <- newMVar
	let typ' = mkGS typ
	addFunc (typ', gfs)

-- simple bind types
-- unary and binary predicates
-- unary and binary functions

class Isomorphic a o | a -> o  where
	to :: a -> o
	from :: o -> a



data L a = LV MVar | V a
	deriving (Eq, Read, Typeable, Data, Show)


instance Wrapable (L a) where
	wrap = LV

--instance Isomorphic a (L a) where
--	to = 	V
--	from (V x) = x


up :: (Isomorphic a o, Wrapable o, Unifiable o) => (a -> Bool) -> o -> M o
up f x = do
	a <- newMVar
	let a' = wrap a
	bind (GFS (f', [x'])) a'
	return a'
	where	x' = mkGS x
		f' = (\[x]->let x'=from (frGS x) 
			in if (f x') then do {m <- newMVar; return (mkGS m);} else mzero)

--return $ mkGS (to (f x')))


bp :: (Isomorphic a o, Wrapable o, Unifiable o) => (a -> a -> Bool) -> o -> o -> M o
bp f x y = do
	a <- newMVar
	let a' = wrap a
	bind (GFS (f', [x',y'])) a'
	return a'
	where	x' = mkGS x
		y' = mkGS y
		f' = (\[x,y]->let x'=from (frGS x) in let y'=from (frGS y) 
			in if (f x' y') then do {m <- newMVar; return (mkGS m);} else mzero)


bf :: (Isomorphic a o, Wrapable o, Unifiable o) => (a -> a -> a) -> o -> o -> M o
bf f x y = do
	--a <- newMVar
	--let a' = wrap a
	a' <- newVar
	bind (GFS (f', [x',y'])) a'
	return a'
	where	x' = mkGS x
		y' = mkGS y
		f' = (\[x,y]->let x'=from (frGS x) in let y'=from (frGS y) 
			in return $ mkGS (to (f x' y')))

bfM :: (Isomorphic a o, Wrapable o, Unifiable o) => (a -> a -> M a) -> o -> o -> M o
bfM f x y = do
	a <- newMVar
	let a' = wrap a
	bind (GFS (f', [x',y'])) a'
	return a'
	where	x' = mkGS x
		y' = mkGS y
		f' = (\[x,y]->let x'=from (frGS x) in let y'=from (frGS y) 
			in do
				v <- f x' y'
				return $ mkGS $ to v
			)

ufM :: (Isomorphic a o, Wrapable o, Unifiable o) => (a -> M a) -> o -> M o
ufM f x = do
	a <- newMVar 
	let a' = wrap a
	bind (GFS (f', [x'])) a'
	return a'
	where	x' = mkGS x
		f' = (\[x]->let x'=from (frGS x)
			in do
				v <- f x'
				return $ mkGS $ to v
			)

uf :: (Isomorphic a o, Wrapable o, Unifiable o) => (a -> a) -> o -> M o
uf f x = do
	a <- newMVar
	let a' = wrap a
	bind (GFS (f', [x'])) a'
	return a'
	where	x' = mkGS x
		f' = (\[x]->let x'=from (frGS x) 
			in return $ mkGS (to (f x')))
		

--say x = unsafePerformIO (putStrLn x)
say x = ()

suppose :: Judgement i o => i -> o -> M ()
suppose expr typ = do
	incr
	mt <- try expr rules
	let mt' = mkGS mt
	let typ' = mkGS typ
	case (gunify mt' typ') of
		(Just x) -> merge x >> return ()
		Nothing -> do {(say "mzero") `seq` mzero;}
--mzero


-- infix notation for suppose
(.>.) :: Judgement i o => i -> o -> M ()
(.>.) = suppose

(.==.) :: Unifiable o => o -> o -> M ()
(.==.) e1 e2 = do
	let e1' = mkGS e1
	let e2' = mkGS e2
	case (gunify e1' e2') of
		(Just x) -> do {merge x; return ();}
		Nothing -> mzero
	

try :: i -> [i -> R o] -> R o
try expr (f:fx) = (say "step" `seq` f expr) `mplus` (try expr fx) 
try expr [] = mzero

consider :: [a] -> R a
consider [] = mzero
consider (a:al) = (return a `mplus` consider al)

pt :: Unifiable o => o -> R o
pt t = do
	let t' = mkGS t
	mgs <- pt' t' 
	return $ frGS mgs	


pt' :: GS -> M GS
pt' t = do
	(_,x,_,_) <- fromState id
	return $ gsub t x

funcs :: [(GS, GFS)] -> M ()
funcs gfx = do
	mapM_ func2 (reverse gfx)
	


func2 (g, GFS (f, pl)) = do
	pl' <- mapM pt' pl
	x <- f pl'
	(say "merge") `seq` merge [(g,x)]

clr = NDSM (\(i,x,z,cnt)->[((i,[],z,cnt),())])

incr = NDSM (\(i,x,z,cnt)->[((i,x,z,succ cnt), ())])

infer :: Judgement i o => i -> [o]
infer expr = eval (try expr rules)

inf :: Judgement i o => i -> [o]
inf e = infer e

eval :: Unifiable o => M o -> [o]
eval x = map snd rsm
	where	rnsm = do { b <- x; (_,_,z,cnt) <- fromState id; 
			funcs z; 
			c <- pt b; return c; }
		rsm = runNDSM rnsm (base, [], [], 1)

