{-# LANGUAGE DataKinds #-}

module Evaluation where

import UserInterface
import Syntax
import Helpers
import Simplify

import Data.Maybe    

-- | Evaluation 1: density of clamped standard normal
-----------------------------------------------------

-- The measure is clamped at 0 and 1
clampedStdNorm :: CH (Term ('HMeasure 'HReal))
clampedStdNorm = bind stdNormal $ \n ->
                 dirac (max_ (Real 0) (min_ (Real 1) n))

-- The base measure: mix tt [0,1]
mixT01 :: Base 'HReal
mixT01 = Mixture True [Real 0, Real 1]

-- | Print the output of base-checking disintegration
-- The `check` function is defined in UserInterface.hs
eval1 :: IO ()
eval1 = do let model = clampedStdNorm >>= pairWithUnit
                                   -- ^^^ make a product measure
           check (evalNames model) mixT01
               -- ^^^^^^^^^ evaluate the State monad `CH` to generate
               -- fresh variables


-- | Evaluation 2: density of two clamped normals wrt each other
----------------------------------------------------------------

-- This is `normal 3 2`, also clamped at 0 and 1
clampedNorm :: CH (Term ('HMeasure 'HReal))
clampedNorm = bind (Normal (Real 3) (Real 2)) $ \n ->
              dirac (max_ (Real 0) (min_ (Real 1) n))

-- | Use our /unrestricted/ density calculator, where the base measure can
-- be a core Hakaru measure
eval2 :: IO ()
eval2 = let point = Real 0.5
                      -- ^^^ calculate density at this point
        in case density (evalNames clampedStdNorm) (evalNames clampedNorm) point of
             -- ^^^^^^^ defined in UserInterface.hs
             Just r -> print r
             Nothing -> putStrLn "eval2: could not find density"

                        
-- | Evaluation 3: mutual information in a discrete-continuous mixture
----------------------------------------------------------------------
-- See `test1` in MutualInfo.hs
--
-- We put this in a separate file because we use (mainline) Hakaru to
-- simplify the output of our new disintegrator


-- | Evaluation 4: importance sampling with a discrete-continuous prior
-----------------------------------------------------------------------

mckayDens :: Term 'HReal -> Term 'HReal
mckayDens x = let (c1,c2) = (Real 0.4, Real 0.08)
              in Exp $         (c1 `mul` (square (x `minus` c1)))
                       `minus` (c2 `mul` (square (square x)))

-- A modified version of the mckay distribution below, where the
-- support is restricted to [0,1], with non-zero mass at 0 and 1
target4 :: CH (Term ('HMeasure 'HReal))
target4 = uniform (Real 0) (Real 1) >>= \unif01 ->
          bind unif01 $ \x ->
          return $ msum_ [ weight (mckayDens x) (Dirac x)
                         , weight (Real 0.37)   (Dirac (Real 0))
                         , weight (Real 0.42)   (Dirac (Real 1)) ]

-- | Derive and print an importance sampler for this example
-- We use the unrestricted density calculator to obtain the
-- "importance weight" for each sample.
eval4 :: IO ()
eval4 = let sampler = do target <- target4
                         proposal <- clampedStdNorm
                         importance target proposal
                      -- ^^^^^^^^^^ defined in UserInterface.hs
        in print . evalNames . shareClampedM $ evalNames sampler
                    

-- | Evaluation 5a: MH-sampling using single-site proposals
-----------------------------------------------------------

mckay :: CH (Term ('HMeasure 'HReal))
mckay = bind Lebesgue $ \x ->
        return $ weight (mckayDens x) (Dirac x)

type R2 = 'HPair 'HReal 'HReal
    
target5a :: CH (Term ('HMeasure R2))
target5a = mckay >>= \m ->
           bindx m (\x -> return (Normal x (Real 1)))

proposal5a :: Term R2 -> CH (Term ('HMeasure R2))
proposal5a p = let (x,y) = (frst p, scnd p)
               in do m1 <- bind (Normal x (Real 0.1)) (\x' -> dirac (Pair x' y))
                     m2 <- bind (Normal y (Real 0.1)) (\y' -> dirac (Pair x y'))
                     return (mplus_ m1 m2)

-- | Derive and print a Metropolis-Hastings-Green kernel for this example.
--
-- The `mhg` function calculates Green's ratio, i.e., the generic
-- acceptance ratio for MCMC sampling, using our unrestricted density
-- calculator.
eval5a :: IO ()
eval5a = let t = Pair (Real 0) (Real 0.5)
         in print $ evalNames $ mhg (evalNames target5a) proposal5a t
                             -- ^^^ defined in UserInterface.hs

-- | Evaluation 5b: MH-sampling using reversible-jump proposals
---------------------------------------------------------------

type RPlusR2 = 'HEither 'HReal R2

target5b :: CH (Term ('HMeasure RPlusR2))
target5b = do m1 <- bind stdNormal $ \x -> dirac (Inl x)
              m2 <- bind stdNormal $ \y ->
                    bind stdNormal $ \z ->
                    dirac (Inr (Pair y z))
              return (mplus_ m1 m2)

proposal5b :: Term RPlusR2 -> CH (Term ('HMeasure RPlusR2))
proposal5b p = do let s = Real 0.1
                  m1 <- letinl p $ \x ->
                        bind (Normal x s) $ \x1 ->
                        bind (Normal x s) $ \x2 ->
                        dirac (Inr (Pair x1 x2))
                  m2 <- letinr p $ \x ->
                        bind (Normal (frst x `add` scnd x) s) $ \x' ->
                        dirac (Inl x')
                  return (mplus_ m1 m2)

-- | Derive and print a Metropolis-Hastings-Green kernel for this example.
-- 
-- In this example the state space is RPlusR2.  The same `mhg`
-- function can be used here as in the previous case, where the state
-- space was R2.
eval5b :: IO ()
eval5b = let t = Inl (Real 0.2)
         in print $ evalNames $ mhg (evalNames target5b) proposal5b t
                      

-- | Evaluation 6: belief update using a clamped observation
------------------------------------------------------------

tobit :: CH (Term ('HMeasure ('HPair 'HReal 'HReal)))
tobit = bind (Normal (Real 3) (Real 2)) $ \x ->
        bind (Normal x (Real 1)) $ \y ->
        dirac (Pair (max_ (Real 0) (min_ (Real 1) y)) x)
         
eval6 :: IO ()
eval6 = check (evalNames tobit) mixT01
                             -- ^^^^^^ same base as eval1


-- | Evaluation 7: Gibbs-sampling a discrete-continuous mixture
---------------------------------------------------------------

type R3 = 'HPair 'HReal R2

tobit3D :: CH (Term ('HMeasure R3))
tobit3D = let clamp y = max_ (Real 0) (min_ (Real 1) y)
          in bind (Normal (Real 3) (Real 2)) $ \x ->
             bind (Normal x (Real 1)) $ \y1' ->
             bind (Normal x (Real 1)) $ \y2' ->
             bind (Normal x (Real 1)) $ \y3' ->
             bind (Dirac (clamp y1')) $ \y1 ->
             bind (Dirac (clamp y2')) $ \y2 ->
             bind (Dirac (clamp y3')) $ \y3 ->
             dirac (Pair y1 (Pair y2 y3))

-- | We will use disintegration to obtain the full conditional
-- distributions for Gibbs sampling.
--
-- Now our disintegrator always conditions on the first dimension of
-- the input joint distribution. Our full conditional distributions
-- will each condition on a pair of variables.
--
-- Thus we will define helper functions that re-order the variables in
-- the target (tobit3D)

-- Re-order so that we can condition on the pair (y2,y3)
obs23 :: CH (Term ('HMeasure ('HPair R2 'HReal)))
obs23 = tobit3D >>= liftMeasure switch

-- Re-order so that we can condition on the pair (y1,y3)
obs13 :: CH (Term ('HMeasure ('HPair R2 'HReal)))
obs13 = tobit3D >>= \model -> bind model $ \p ->
        dirac (Pair (Pair (frst p) (scnd (scnd p))) (frst (scnd p)))

-- Re-order so that we can condition on the pair (y1,y2)
obs12 :: CH (Term ('HMeasure ('HPair R2 'HReal)))
obs12 = tobit3D >>= \model -> bind model $ \p ->
        dirac (Pair (Pair (frst p) (frst (scnd p))) (scnd (scnd p)))

base6 :: Base R2
base6 = Bindx mixT01 (const mixT01) -- ^ 2D-discrete-continuous mixture

-- | Write a Gibbs sampler for this example
-- We use `condition`, defined in UserInterface.hs, to calculate the
-- full conditional distributions using disintegration.
gibbs :: Term R3 -> CH (Term ('HMeasure R3))
gibbs p = do model23 <- obs23
             model13 <- obs13
             model12 <- obs12
             case condition model23 base6 (scnd p) of
               Just m1 -> bind m1 $ \q1 ->
                          case condition model13 base6 (Pair q1 (scnd (scnd p))) of
                            Just m2 -> bind m2 $ \q2 ->
                                       case condition model12 base6 (Pair q1 q2) of
                                         Just m3 -> bind m3 $ \q3 ->
                                                    dirac (Pair q1 (Pair q2 q3))
                                         Nothing -> error "gibbs: conditional3 failed"
                            Nothing -> error "gibbs: conditional2 failed"
               Nothing -> error "gibbs: conditional1 failed"
                           
eval7 :: IO ()
eval7 = print $ evalNames $ gibbs $ Pair (Real 1.1) $ Pair (Real 1.2) (Real 1.3)

        
-- | Evaluation 8: Single-site MH for Gaussian Mixture Model
------------------------------------------------------------

gmm :: CH (Term ('HMeasure ('HPair R2 R2)))
gmm = bind meandist1 $ \mu1 ->
      bind meandist2 $ \mu2 ->
      bind faircoin  $ \b1 ->
      bind faircoin  $ \b2 ->
      bind (mixture b1 mu1 mu2) $ \p1 ->
      bind (mixture b2 mu1 mu2) $ \p2 ->
      dirac $ Pair (Pair p1 p2) (Pair mu1 mu2)
    where meandist1 = Normal (Real 2) (Real 3)
          meandist2 = Normal (Real 5) (Real 3)
          faircoin = bern_ (Real 0.5)
          mixture b c1 c2 = if_ b (Normal c1 (Real 1)) (Normal c2 (Real 1))

target8 :: Maybe (Term ('HMeasure R2))
target8 = do let t = Pair (Real 0.1) (Real 0.2)
                 m = monadRightId $ evalNames gmm
             b <- principalBase m t
             condition m b t

-- TODO: investigate
-- Why does changing x from actual numbers to a variable (Var (V "curr_x"))
-- break the program with the "Unequal types of associated terms..." error?
eval8 :: IO ()
eval8 = let x = Pair (Real 0.1) (Real 0.2)
        in print $
           monadRightId $
           evalNames $
           mhgWithLets (fromJust target8) proposal5a x
                                       -- ^^^^^^^^^^ single-site
