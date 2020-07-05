module NDSM where

import Control.Monad
import GHC.Base

newtype NDSM s a = NDSM {unNDSM :: (s -> [(s,a)])}

instance Functor (NDSM s) where
    fmap f x = undefined

instance Applicative (NDSM s) where
    pure = return
    f <*> x = undefined

instance Monad (NDSM s) where
    return x = NDSM (\s -> [(s,x)])
    (NDSM f) >>= c = NDSM (\s ->
        let svl = f s
            ml = map (\(_,x)->(unNDSM $ c x)) svl
            sl = map fst svl
            aml = zipWith ($) ml sl
        in concat aml)

instance Alternative (NDSM s) where
    empty = mzero
    (<|>) = mplus

instance MonadPlus (NDSM s) where
    mzero = NDSM (const [])
    mplus (NDSM x) (NDSM y) = NDSM (\s->(x s)++(y s))

onState :: (s -> s) -> NDSM s ()
onState f = NDSM (\s->[(f s,())])

fromState :: (s -> a) -> NDSM s a
fromState f = NDSM (\s->[(s, f s)])

runNDSM :: NDSM s a -> s -> [(s,a)]
runNDSM (NDSM f) = f
