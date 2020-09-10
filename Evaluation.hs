{-# LANGUAGE DataKinds #-}

module Evaluation where

import UserInterface
import Syntax
import Helpers
import Simplify
import Hakaru    

import Data.Maybe
import Debug.Trace    

import qualified Language.Hakaru.Simplify as S
import qualified Language.Hakaru.Pretty.Haskell as PH

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

type B2 = 'HPair HBool HBool
type R2B2 = 'HPair R2 B2    

gmm :: CH (Term ('HMeasure ('HPair R2B2 R2)))
gmm = bind meandist1 $ \mu1 ->
      bind meandist2 $ \mu2 ->
      bind faircoin  $ \b1 ->
      bind faircoin  $ \b2 ->
      bind (mixture b1 mu1 mu2) $ \p1 ->
      bind (mixture b2 mu1 mu2) $ \p2 ->
      dirac $ Pair (Pair (Pair p1 p2) (Pair b1 b2)) (Pair mu1 mu2)
    where meandist1 = Normal (Real 2) (Real 3)
          meandist2 = Normal (Real 5) (Real 3)
          faircoin = bern_ (Real 0.5)
          mixture b c1 c2 = if_ b (Normal c1 (Real 1)) (Normal c2 (Real 1))

target8 :: CH (Maybe (Term ('HMeasure R2)))
target8 = do let t = Pair (Pair (Real 0.1) (Real 0.2)) (Pair true_ false_)
             m <- monadRightId <$> gmm
             return $ do b <- principalBase "target8 " m t
                         condition m b t

-- TODO: investigate
-- Why does changing x from actual numbers to a variable (Var (V "curr_x"))
-- break the program with the "Unequal types of associated terms..." error?
eval8 :: IO ()
eval8 = let x = Pair (Real 0.1) (Real 0.2)
        in print $
           monadRightId $
           evalNames $
           mhg3 (fromJust <$> target8) proposal5a (return x)
                                       -- ^^^^^^^^^^ single-site

-- See what base measure we deal with to calculate Green's ratio
peek8 :: IO ()
peek8 = let m    = fromJust <$> target8 >>= \t -> bindx t proposal5a
            mrev = m >>= liftMeasure switch
            m'   = m >>= pairWithUnit
            mrev'= mrev >>= pairWithUnit
        in do print $ allBases (evalNames m') $
                      Pair (Pair (Real 0.37) (Real 0.42))
                           (Pair (Real 0.39) (Real 0.19))
              print $ allBases (evalNames mrev') $
                      Pair (Pair (Real 0.37) (Real 0.42))
                           (Pair (Real 0.39) (Real 0.19))

ratio8 :: IO ()
ratio8 = do let x = Pair (Real 0.37) (Real 0.42)
                y = Pair (Real 0.37) (Real 0.19)
                Just (n,d) = evalNames $
                             do t <- target8
                                return $ greensRatio (fromJust t) proposal5a (Pair x y)
            putStrLn "----denominator-------"
            print d
            denomSimplWithoutTotal <- S.simplifyDebug False 30 (translate d)
            putStrLn "----denominator simplified------"
            print $ PH.pretty denomSimplWithoutTotal
            denomSimplWithTotal <- S.simplifyDebug False 30 (translate $ Total d)
            putStrLn "----denominator simplified after total------"
            print $ PH.pretty denomSimplWithTotal
            ratioSimpl <- S.simplifyDebug False 30 (translate $ ratio2Real (n,d))
            putStrLn "----ratio simplified------"
            print $ PH.pretty ratioSimpl

ratio8Symbolic :: IO ()
ratio8Symbolic = do let nm = "some_unused_name"
                        xy = V nm
                        mayberatio = evalNames $
                                     do t <- target8
                                        return $ greensRatio (fromJust t) proposal5a (Var xy)
                    print $ isJust mayberatio

-- | Evaluation 9: Reversible-jump MH for Finite Mixture Model
--------------------------------------------------------------

type NParamsType = 'HPair 'HReal 'HReal -- (mu, sigma^2)
type NParamType = 'HReal  -- if we only care about the mean
type OneNormal  = NParamsType
type TwoNormals = 'HPair NParamsType NParamsType
type FM = 'HEither OneNormal TwoNormals

-- finiteMixtureModel :: Term ('HMeasure ('HPair 'HReal FM))
-- finiteMixtureModel = MPlus (do_ [ m1 :<~ stdNormal
--                                 , s1 :<~ stdNormal
--                                 , n :<~ Normal (Var m1) (Var s1) ]
--                                 (Dirac (Pair (Var n) (Inl (Pair (Var m1) (Var s1))))))
--                            (do_ [ m1 :<~ stdNormal
--                                 , s1 :<~ stdNormal
--                                 , m2 :<~ stdNormal
--                                 , s2 :<~ stdNormal
--                                 , n :<~ MPlus (Normal (Var m1) (Var s1))
--                                               (Normal (Var m2) (Var s2)) ]
--                                 (Dirac (Pair (Var n) (Inr (Pair (Pair (Var m1) (Var s1))
--                                                                 (Pair (Var m2) (Var s2)))))))
--     where (m1,s1,m2,s2,n) = (V "m1", V "s1", V "m2", V "s2", V "n")

fmm :: CH (Term ('HMeasure ('HPair 'HReal FM)))
fmm = do let s = Real 0.1
         m1 <- bind stdNormal $ \mu ->
               bind stdNormal $ \v ->
               bind (Normal mu (sqrroot v)) $ \x ->
               dirac (Pair x (Inl (Pair mu v)))
         m2 <- bind stdNormal $ \mu1 ->
               bind stdNormal $ \v1 ->
               bind stdNormal $ \mu2 ->
               bind stdNormal $ \v2 ->
               bind (mplus_ (Normal mu1 (sqrroot v1))
                            (Normal mu2 (sqrroot v2))) $ \x ->
               dirac (Pair x (Inr (Pair (Pair mu1 v1) (Pair mu2 v2))))
         return $ mplus_ m1 m2

target9 :: CH (Maybe (Term ('HMeasure FM)))
target9 = do m <- monadRightId <$> fmm
             let t = Real 0.43 -- (Var obs)
             return $ do b <- principalBase "target9 " m t
                         condition m b t

-- Moment matching with split-merge moves
-- https://arxiv.org/pdf/1001.2055.pdf , eqs. 1.2.3 and 1.2.4
proposal9 :: Term FM -> CH (Term ('HMeasure FM))
proposal9 p = do let s = Real 0.1
                 m1 <- letinl p $ \x ->
                       bind (Dirac (frst x)) $ \mu ->
                       bind (Dirac (scnd x)) $ \v  ->
                       stdUniform >>= \unif1 ->
                       stdUniform >>= \unif1' ->
                       stdUniform >>= \unif2 ->
                       stdUniform >>= \unif2' ->
                       bind unif1 $ \u1  ->
                       bind unif1' $ \u1' ->
                       bind unif2 $ \u2 ->
                       bind unif2' $ \u2' ->
                       bind (Dirac (mu `minus` (u1 `mul` (sqrroot v)))) $ \mu1 ->
                       bind (Dirac (mu `add`   (u2 `mul` (sqrroot v)))) $ \mu2 -> 
                       bind (Dirac (                  u1'  `mul` ((Real 1) `minus` (square u1)) `mul` (double v))) $ \v1 ->
                       bind (Dirac (((Real 1) `minus` u2') `mul` ((Real 1) `minus` (square u2)) `mul` (double v))) $ \v2 ->
                       dirac $ Inr $ Pair (Pair mu1 v1) (Pair mu2 v2)
                 m2 <- letinr p $ \x ->
                       bind (Dirac (frst x)) $ \muv1 ->
                       bind (Dirac (frst muv1)) $ \mu1 ->
                       bind (Dirac (scnd muv1)) $ \v1 ->
                       bind (Dirac (scnd x)) $ \muv2 ->
                       bind (Dirac (frst muv2)) $ \mu2 ->
                       bind (Dirac (scnd muv2)) $ \v2 ->
                       bind (Normal ((Real 0.5) `mul` (mu1 `add` mu2)) s) $ \mu ->
                       bind (Normal ((Real 0.25) `mul` (square $ mu1 `minus` mu2) `add` (Real 0.5) `mul` (square v1 `add` square v2)) s) $ \v ->
                       dirac $ Inl $ Pair mu v
                 return $ monadRightId $ mplus_ m1 m2

eval9 :: IO ()
eval9 = let x = Inl (Pair (Real 2) (Real 3))
        in print $
           mplusId $
           monadRightId $
           evalNames $                           
           mhg3 (fromJust <$> target9) proposal9 (return x) -- (Var <$> freshVar "currX")

-- See what base measure we deal with to calculate Green's ratio
peek9 :: IO ()
peek9 = let m    = fromJust <$> target9 >>= \t -> bindx t proposal9
            mrev = m >>= liftMeasure switch
            m'   = m >>= pairWithUnit
            mrev'= mrev >>= pairWithUnit
            x  = Inl (Pair (Real 2) (Real 3))
            x' = Inr (Pair (Pair (Real 1) (Real 5))
                           (Pair (Real 3) (Real 7)))
        in do print $ allBases (evalNames m') (Pair x x')
              putStrLn "-----"
              print $ allBases (evalNames mrev') (Pair x' x)
              putStrLn "-----"
              print $ allBases (evalNames m') (Pair x x)

ratio9 :: IO ()
ratio9 = do let x = Inl (Pair (Real 2) (Real 3))
                y = Inr (Pair (Pair (Real 1) (Real 2))
                              (Pair (Real 5) (Real 7)))
                Just (n,d) = evalNames $
                             do t <- target9
                                return $ greensRatio (fromJust t) proposal9 (Pair x y)
            print d
            -- putStrLn "demarcation after core Hakaru"
            -- print . translate $ d            
            -- putStrLn "demarcation before total"
            -- print . translate $ Total d
            putStrLn "demarcation before simplify without total"
            denomSimplWithoutTotal <- S.simplifyDebug False 30 (translate d)
            -- print denomSimplWithoutTotal
            print $ PH.pretty denomSimplWithoutTotal
