-- ** GENERIC UNIFICATION
{-#LANGUAGE DeriveDataTypeable#-}

module TypeGU where

import Control.Monad
import Data.List
import Data.Maybe

import Data.Generics

import System.IO.Unsafe (unsafePerformIO)

-- *****************
-- NOTE: The following must be present for use in GHC 6.4
-- remove them for use in GHC 6.2
conFixity = constrFixity
conString = showConstr
-- *****************



-- the type Constr doesn't work right in Eq
-- so we define our own type to represent this

-- CS isInfix name
data CS = CS {csInfix :: Bool,  csName :: String }
    deriving (Eq, Show, Typeable, Data)

toCS :: Constr -> CS
toCS x | conFixity x == Infix = CS True (conString x)
toCS x | otherwise = CS False (conString x)

data GS = GSVar Int | GSCons CS [GS] | GSInt Int | GSChar Char
    deriving (Eq, Show, Typeable, Data)

-- This type must be used to represent unifiable variables
-- by the clients
newtype MVar = MVar Int
    deriving (Eq, Typeable, Data, Read, Show)

instance Enum MVar where
    fromEnum (MVar x) = x
    toEnum x = MVar x

base = MVar 0

class (Eq a, Data a, Read a) => Unifiable a

instance Unifiable MVar where


mkGS :: Data a => a -> GS
mkGS x | isJust ((cast x)::Maybe Int) = GSInt (fromJust ((cast x)::Maybe Int))
mkGS x | isJust ((cast x)::Maybe Char) = GSChar (fromJust ((cast x)::Maybe Char))
mkGS x | (csName $ toCS $ toConstr x) == "MVar" =
    GSVar ((fromJust.head) (gmapQ cast x))
mkGS x = GSCons (toCS $ toConstr x) (gmapQ mkGS x)





-- problem:
-- extractstruct must accumulate all non-a (ft)
-- things so that frgs doesn't get called on them
frGS :: Read a => GS -> a
frGS x = 
--  unsafePerformIO (do {putStrLn (show x); putStrLn ((s x)); return (read (s x));})
--
    read (s x)
    where  
        s (GSCons x rl) =
            case (csInfix x) of
                False -> (csName x) ++ " " ++ rs rl
                True -> case (csName x) of
                    "(:)" -> "["++mkList rl++"]"
                    csx -> "("++(s (head rl))++" "++
                        [head (tail csx)]++
                        " "++(s (last rl))++")"
        s (GSVar x) = "MVar "++(show x)
        s (GSInt x) = show x
        s (GSChar x) = show x
        
        rs rl = concatMap (\x->let sx = s x in (case (head sx) of
                '[' -> sx++" "
                _ -> "("++sx++") ")
                ) rl
        
        mkList :: [GS] -> String
        mkList [x, (GSCons m y)] | csName m == "(:)" = 
            (s x)++","++(mkList y)
        mkList [x, y] = (s x)






gunify :: GS -> GS -> Maybe [(GS,GS)]
gunify x y | x == y = Just []
gunify x@(GSCons _ [GSVar _]) y | not (gIsIn x y) = Just [(x,y)]
gunify x y@(GSCons _ [GSVar _]) | not (gIsIn y x) = Just [(y,x)]
gunify (GSCons m1 rl1) (GSCons m2 rl2) | m1 == m2 = do
    um <- mapM (uncurry gunify) (zip rl1 rl2)
    foldM gasl [] um
gunify _ _ = Nothing
    

gIsIn :: GS -> GS -> Bool
gIsIn x y | x == y = True
gIsIn x (GSCons _ rl) = any (==True) (map (gIsIn x) rl)
gIsIn _ _ = False


gHasVars :: GS -> Bool
gHasVars (GSCons _ rl) = any id (map gHasVars rl)
gHasVars (GSVar _) = True
gHasVars _ = False

gasl :: [(GS,GS)] -> [(GS,GS)] -> Maybe [(GS,GS)]
gasl xs ys = do
    xys <- gasl' xs ys
    case (findmapair xys) of
        Nothing -> return xys
        (Just p) -> gumapair xys p


gasl' :: [(GS,GS)] -> [(GS,GS)] -> Maybe [(GS,GS)]
gasl' xs (yp:ys) = do
    r <- gasl xs ys
    return $ (gsubs yp xs):r
gasl' x [] = return x


gumapair :: [(GS,GS)] -> (GS,GS,GS) -> Maybe [(GS,GS)]
gumapair xl (x,z1,z2) = ur
    where  
        xl' = xl \\ [(x,z1)] -- (x,z2)
        ur  = case (gunify z1 z2) of
                (Just x) -> gasl x xl'
                Nothing -> Nothing



gsub :: GS -> [(GS,GS)] -> GS
gsub = foldi gsub1

gsub1 :: GS -> (GS,GS) -> GS
gsub1 t (x,y) | t == x = y
gsub1 (GSCons m rl) xy = GSCons m (map (\q->(gsub1 q xy)) rl)
gsub1 t _ = t
--gsub1 t (x,y) = sub t x y

sub :: (Data a, Eq a) => a -> a -> a -> a
sub x t t' = everywhere (mkT (\y->if y == t then t' else y)) x



-- first: item
-- second: subtitution to apply
gsubs1 :: (GS,GS) -> (GS,GS) -> (GS,GS)
gsubs1 (x2,y2) xy1 = (x2,gsub1 y2 xy1)


gsubs :: (GS,GS) -> [(GS,GS)] -> (GS,GS)
gsubs = foldi gsubs1

foldi :: Eq a => (a -> b -> a) -> a -> [b] -> a
foldi f b rl = if (r == r')  then r else foldi f r' rl 
    where
        r = foldl f b rl
        r' = foldl f r rl

gbiasl :: [(GS,GS)] -> [(GS,GS)] -> Maybe [(GS,GS)]
gbiasl xs ys = do
    xys <- gasl xs ys
    xys' <- gasl ys xys
    return (remdup xys')

remdup :: Eq a => [(a,a)] -> [(a,a)]
remdup xl = filter (\(x,y)->(x /= y)) (nub xl)

findmapair :: (Eq a) => [(a,a)] -> Maybe (a,a,a)
findmapair xl = if null ac then Nothing else Just $ head ac
    where ac = [(x,z1,z2) | (x,z1) <- xl, (y,z2) <- xl, x == y, z1 /= z2]




