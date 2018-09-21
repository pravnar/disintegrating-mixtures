{-# LANGUAGE DataKinds #-}

module Evaluation where

import Tests
import Syntax
import Helpers

-- | Evaluation 1: density of clamped standard normal
-----------------------------------------------------

-- The measure is clamped at 0 and 1
clampedStdNorm :: CH (Term ('HMeasure 'HReal))
clampedStdNorm = bind stdNormal $ \n ->
                 return $ Dirac (max_ (Real 0) (min_ (Real 1) n))

-- The base measure: mix tt [0,1]
mixT01 :: Base 'HReal
mixT01 = Mixture True [Real 0, Real 1]

eval1 :: IO ()
eval1 = do let model = clampedStdNorm >>= pairWithUnit
                                   -- ^^^ make a product measure
           check (evalNames model) mixT01
               -- ^^^^^^^^^^^^^^^ evaluate the State monad `CH` to
               -- generate fresh variables


-- | Evaluation 2: density of two clamped normals wrt each other
----------------------------------------------------------------

-- This is `normal 3 2`, also clamped at 0 and 1
clampedNorm :: CH (Term ('HMeasure 'HReal))
clampedNorm = bind (Normal (Real 3) (Real 2)) $ \n ->
              return $ Dirac (max_ (Real 0) (min_ (Real 1) n))

eval2 :: IO ()
eval2 = let point = Real 0.5
                      -- ^^^ calculate density at this point
        in case density (evalNames clampedStdNorm) (evalNames clampedNorm) point of
             -- ^^^^^^^ use /unrestricted/ density calculator, where
             -- the base measure can be a core Hakaru measure
             Just r -> print r
             Nothing -> putStrLn "eval2: could not find density"

                        
-- | Evaluation 3: mutual information in a discrete-continuous mixture
----------------------------------------------------------------------
-- See MutualInfo.hs


-- | Evaluation 4: importance sampling with a discrete-continuous prior
-----------------------------------------------------------------------
-- TODO


-- | Evaluation 5a: MH-sampling using single-site proposals
-----------------------------------------------------------

mckay :: CH (Term ('HMeasure 'HReal))
mckay = bind Lebesgue $ \x ->
        let (c1,c2) = (Real 0.4, Real 0.08)
        in return $ weight (Exp $        (c1 `mul` (square (x `minus` c1)))
                                 `minus` (c2 `mul` (square (square x))))
                           (Dirac x)

type R2 = 'HPair 'HReal 'HReal
    
target5a :: CH (Term ('HMeasure R2))
target5a = mckay >>= \m ->
           bindx m (\x -> return (Normal x (Real 1)))

proposal5a :: Term R2 -> CH (Term ('HMeasure R2))
proposal5a p = let (x,y) = (frst p, scnd p)
               in do m1 <- bind (Normal x (Real 0.1)) (\x' -> return (Dirac (Pair x' y)))
                     m2 <- bind (Normal y (Real 0.1)) (\y' -> return (Dirac (Pair x y')))
                     return (mplus_ m1 m2)

eval5a :: IO ()
eval5a = let t = Pair (Pair (Real 0) (Real    0.5))
                      (Pair (Real 0) (Real $ -0.5))
         in case greensRatio (evalNames target5a) proposal5a t of
              Just r -> print r
              Nothing -> putStrLn "eval5a: could not calculate acceptance ratio"


-- | Evaluation 5b: MH-sampling using reversible-jump proposals
---------------------------------------------------------------

type RPlusR2 = 'HEither 'HReal R2

target5b :: CH (Term ('HMeasure RPlusR2))
target5b = do m1 <- bind stdNormal $ \x -> return (Dirac (Inl x))
              m2 <- bind stdNormal $ \y ->
                    bind stdNormal $ \z ->
                    return $ Dirac (Inr (Pair y z))
              return (mplus_ m1 m2)

proposal5b :: Term RPlusR2 -> CH (Term ('HMeasure RPlusR2))
proposal5b p = do let s = Real 0.1
                  m1 <- letinl p $ \x ->
                        bind (Normal x s) $ \x1 ->
                        bind (Normal x s) $ \x2 ->
                        return $ Dirac (Inr (Pair x1 x2))
                  m2 <- letinr p $ \x ->
                        bind (Normal (frst x `add` scnd x) s) $ \x' ->
                        return $ Dirac (Inl x')
                  return (mplus_ m1 m2)

eval5b :: IO ()
eval5b = case greensRatio (evalNames target5b) proposal5b (Var (V "t")) of
           Just r -> print r
           Nothing -> putStrLn "eval5b: could not calculate acceptance ratio"
                      

-- | Evaluation 6: belief update using a clamped observation
------------------------------------------------------------

tobit :: CH (Term ('HMeasure ('HPair 'HReal 'HReal)))
tobit = bind (Normal (Real 3) (Real 2)) $ \x ->
        bind (Normal x (Real 1)) $ \y ->
        return $ Dirac (Pair x (max_ (Real 0) (min_ (Real 1) y)))
         
eval6 :: IO ()
eval6 = check (evalNames tobit) mixT01
                             -- ^^^^^^ same base as eval1


-- | Evaluation 7: Gibbs-sampling a discrete-continuous mixture
---------------------------------------------------------------
-- TODO
