{-# LANGUAGE DataKinds, GADTs #-}

module Tests where

import Syntax
import Helpers
import UserInterface
import Simplify

import Test.HUnit
-- import           Debug.Trace

type Model a b = Term ('HMeasure ('HPair a b))

freeVarFail :: Model 'HReal 'HUnit
freeVarFail = Dirac (Pair (Var (V "x")) Unit)

plusFail :: Model 'HReal 'HUnit
plusFail = Do (x :<~ stdNormal)
              (Dirac (Pair (Add (Var x) (Var x)) Unit))
    where x = V "x"

normTest :: Model 'HReal 'HUnit
normTest = Do (n :<~ stdNormal)
              (Dirac (Pair (Var n) Unit))
    where n = V "n"

unitCircle :: Model 'HReal 'HUnit
unitCircle = do_ [ x :<~ stdNormal
                 , y :<~ stdNormal ]
                 (Dirac (Pair (Sqrt (Add (Square (Var x))
                                         (Square (Var y))))
                              Unit))
    where (x,y) = (V "x", V "y")
                    
gaussMix :: Model 'HReal ('HPair 'HReal 'HReal)
gaussMix = Do (mu1 :<~ stdNormal)
              (Do (mu2 :<~ stdNormal)
                  (Do (x :<~ MPlus (Normal (Var mu1) (Real 1))
                                   (Normal (Var mu2) (Real 1)))
                      (Dirac (Pair (Var x)
                                   (Pair (Var mu1) (Var mu2))))))
    where (mu1, mu2, x) = (V "mu1", V "mu2", V "x")

helloWorld :: Model 'HReal 'HReal
helloWorld = do_ [ mu :<~ stdNormal
                 , x  :<~ Normal (Var mu) (Real 1) ]                      
                 (Dirac (Pair (Var x) (Var mu)))
    where (mu, x) = (V "mu", V "x")

helloProposal :: Term 'HReal -> Term ('HMeasure 'HReal)
helloProposal x = Normal x (Real 0.5)
              

helloWorld2D :: Model ('HPair 'HReal 'HReal) 'HReal
helloWorld2D = do_ [ mu :<~ stdNormal
                   , x  :<~ Normal (Var mu) (Real 1)
                   , y  :<~ Normal (Var mu) (Real 1) ]
                   (Dirac (Pair (Pair (Var x) (Var y)) (Var mu)))
    where (mu, x, y) = (V "mu", V "x", V "y")

density2D :: Model ('HPair 'HReal 'HReal) 'HUnit
density2D = do_ [ x  :<~ Normal (Real 0) (Real 1)
                , y  :<~ Normal (Var x)  (Real 1) ]
                (Dirac (Pair (Pair (Var y) (Var x)) Unit))
    where (x, y) = (V "x", V "y")

unclampedGPA :: Model 'HReal ('HEither 'HUnit 'HUnit)
unclampedGPA = MPlus (Do (x :<~ Normal (Real 2) (Real 3))
                         (Dirac (Pair (Var x) true_)))
                     (Do (y :<~ Normal (Real 5) (Real 6))
                         (Dirac (Pair (Var y) false_)))
    where (x,y) = (V "x", V "y")

-- | Examples that produce base-constraints containing term-language variables
-------------------------------------------------------------------------------
lubAndMPlus :: Model 'HReal 'HUnit
lubAndMPlus = do_ [ x :<~ stdNormal
                  , y :<~ MPlus (Normal (Var x) (Real 1))
                                (Dirac (Real 0)) ]
             (Dirac (Pair (Add (Var x) (Var y)) Unit))
    where (x,y) = (V "x", V "y")

addAdd :: Model 'HReal 'HUnit
addAdd = do_ [ x :<~ stdNormal
             , y :<~ stdNormal ]
         (Dirac (Pair (Add (Var y) (Add (Var x) (Var x))) Unit))
    where (x,y) = (V "x", V "y")

plus :: Model 'HReal 'HUnit
plus = Do (x :<~ stdNormal)
          (Dirac (Pair (Add (Var x) (Var x)) Unit))
    where x = (V "x")
-------------------------------------------------------------------------------

discrete2 :: Model 'HReal 'HUnit
discrete2 = msum_ [Dirac (Pair (Real r) Unit) | r <- [1..3]]

gpa :: Model 'HReal ('HEither 'HUnit 'HUnit)
gpa = Do (n :<~ Normal (Real 2) (Real 3))
         (MPlus (if_ (Less (Var n) (Real 4))
                     (if_ (leq (Var n) (Real 0))
                          (Dirac (Pair (Real 0) true_))
                          (Dirac (Pair (Var n) true_)))
                     (Dirac (Pair (Real 4) true_)))
                (if_ (Less (Var n) (Real 10))
                     (if_ (leq (Var n) (Real 0))
                          (Dirac (Pair (Real 0) false_))
                          (Dirac (Pair (Var n) false_)))
                     (Dirac (Pair (Real 10) false_))))
    where n = V "n"

gpaWu :: CH (Model 'HReal ('HEither 'HUnit 'HUnit))              
gpaWu = uniform (Real 0) (Real 4) >>= \usaDist ->
        uniform (Real 0) (Real 10) >>= \indiaDist ->
        return $
        mplus_ (Do (g :<~ mplus_ (weight (Real 0.01) (Dirac (Real 4)))
                                 (weight (Real 0.99) usaDist))
                   (Dirac (Pair (Var g) true_)))
               (Do (g :<~ mplus_ (weight (Real 0.01) (Dirac (Real 10)))
                                 (weight (Real 0.99) indiaDist))
                   (Dirac (Pair (Var g) false_)))
    where g = V "g"

-- | 2D Gaussian Mixture Model with 2 clusters
-- We want to do unsupervised learning, i.e., having observed two points
-- we want to infer a distribution over their cluster labels and the cluster means

type R2 = 'HPair 'HReal 'HReal
type B2 = 'HPair HBool HBool
    
gmm :: CH (Model R2 ('HPair B2 R2))
gmm = bind meandist $ \mu1 ->
      bind meandist $ \mu2 ->
      bind faircoin $ \b1 ->
      bind faircoin $ \b2 ->
      bind (mixture b1 mu1 mu2) $ \p1 ->
      bind (mixture b2 mu1 mu2) $ \p2 ->
      dirac $ Pair (Pair p1 p2) (Pair (Pair b1 b2) (Pair mu1 mu2))
    where meandist = Normal (Real 2) (Real 3)
          faircoin = bern_ (Real 0.5)
          mixture b c1 c2 = if_ b (Normal c1 (Real 1)) (Normal c2 (Real 1))
    
clampNorm :: Model 'HReal 'HReal
clampNorm = Do (n :<~ Normal (Real 2) (Real 3))
               (if_ (Less (Var n) (Real 0))
                    (Dirac (Pair (Real 0) (Var n)))
                    (Dirac (Pair (Var n) (Var n))))
    where n = V "n"

truncatedNorm :: Model 'HReal 'HReal
truncatedNorm = do_ [ n :<~ Normal (Real 0) (Real 1)
                    , observe (Less (Var n) (Real 0)) ]
                (Dirac (Pair (Var n) (Var n)))
    where n = V "n"

sqrNorm :: Model 'HReal 'HUnit
sqrNorm = Do (n :<~ Normal (Sqrt (Real 2.6)) (Sqrt (Real 0.1)))
             (Dirac (Pair (Square (Var n)) Unit))
    where n = V "n"

eitherTest :: Model ('HEither 'HUnit 'HUnit) 'HUnit
eitherTest = Dirac (Pair (Inl Unit) Unit)

sometimesPerturb :: Model ('HPair 'HReal 'HReal) 'HUnit
sometimesPerturb = do_ [ x :<~ Normal (Real 0) (Real 1)
                       , y :<~ mplus_ (Normal (Var x) (Real 1))
                                      (Dirac (Var x)) ]
                   (Dirac (Pair (Pair (Var x) (Var y)) Unit))
    where (x, y) = (V "x", V "y")
                  
sometimesDouble :: Model ('HPair 'HReal 'HReal) 'HUnit
sometimesDouble = do_ [ x :<~ Normal (Real 0) (Real 1)
                      , y :<~ mplus_ (Dirac (double (Var x)))
                                     (Dirac (Var x)) ]
                   (Dirac (Pair (Pair (Var x) (Var y)) Unit))
    where (x, y) = (V "x", V "y")                      

-- | MCMC
--------------------------------------------------------------------------------

singleSiteProposal :: Model ('HPair ('HPair 'HReal 'HReal) ('HPair 'HReal 'HReal)) 'HUnit
singleSiteProposal = do_ [ x :<~ stdNormal
                         , y :<~ stdNormal
                         , p :<~ MPlus (Do (x' :<~ Normal (Var x) (Real 0.1))
                                           (Dirac (Pair (Var x' :: Term 'HReal) (Var y :: Term 'HReal))))
                                       (Do (y' :<~ Normal (Var y) (Real 0.1))
                                           (Dirac (Pair (Var x) (Var y')))) ]
                         (Dirac (Pair (Pair (Pair (Var x) (Var y))
                                            (Var p))
                                      Unit))
    where (x,y,x',y',p) = (V "x", V "y", V "x'", V "y'", V "p") 

singleSiteBase :: Base ('HPair ('HPair 'HReal 'HReal) ('HPair 'HReal 'HReal))
singleSiteBase = Bindx (Bindx Lebesgue_ (const Lebesgue_))
                       (\p -> Bindx (Mixture True [frst p])
                                    (const $ Mixture True [scnd p]))

singleSiteProposalSwap :: Model ('HPair ('HPair 'HReal 'HReal) ('HPair 'HReal 'HReal)) 'HUnit
singleSiteProposalSwap = do_ [ x :<~ stdNormal
                             , y :<~ stdNormal
                             , p :<~ MPlus (Do (x' :<~ Normal (Var x) (Real 0.1))
                                               (Dirac (Pair (Var x' :: Term 'HReal) (Var y :: Term 'HReal))))
                                           (Do (y' :<~ Normal (Var y) (Real 0.1))
                                               (Dirac (Pair (Var x) (Var y')))) ]
                             (Dirac (Pair (Pair (Var p)
                                                (Pair (Var x) (Var y)))
                                          Unit))
    where (x,y,x',y',p) = (V "x", V "y", V "x'", V "y'", V "p")

-- singleSiteBaseSwap :: Base ('HPair ('HPair 'HReal 'HReal) ('HPair 'HReal 'HReal))
-- singleSiteBaseSwap = Bindx 

proposal1 :: Model ('HPair 'HReal 'HReal) 'HUnit
proposal1 = do_ [ x :<~ stdNormal
                , y :<~ MPlus (Normal (Var x) (Real 0.1))
                              (Dirac (Var x)) ]
            (Dirac (Pair (Pair (Var x) (Var y)) Unit))
    where (x,y) = (V "x", V "y")

proposal1Swap :: Model ('HPair 'HReal 'HReal) 'HUnit
proposal1Swap = do_ [ x :<~ stdNormal
                    , y :<~ MPlus (Normal (Var x) (Real 0.1))
                                  (Dirac (Var x)) ]
                (Dirac (Pair (Pair (Var y) (Var x)) Unit))
    where (x,y) = (V "x", V "y")

base1 :: Base ('HPair 'HReal 'HReal)
base1 = Bindx Lebesgue_ (\x -> Mixture True [x])      

test2 :: Model 'HReal 'HReal
test2 = do_ [ x :<~ stdNormal
            , y :<~ MPlus (Normal (Var x) (Real 0.1))
                          (Dirac (Var x)) ]
            (Dirac (Pair (Var y) (Var x)))
    where (x,y) = (V "x", V "y")

test3 :: Model ('HPair 'HReal 'HReal) 'HUnit
test3 = do_ [ x  :<~ stdNormal
            , x' :<~ stdNormal
            , y :<~ MPlus (Normal (Var x) (Real 0.1))
                          (Dirac (Var x')) ]
            (Dirac (Pair (Pair (Var x) (Var y)) Unit))
    where (x,x',y) = (V "x", V "x'", V "y")                             

detCorr :: Model ('HPair 'HReal 'HReal) 'HUnit
detCorr = do_ [ x :<~ stdNormal
              , y :<~ Dirac (Exp (Var x)) ]
          (Dirac (Pair (Pair (Var x) (Var y)) Unit))
    where (x,y) = (V "x", V "y")

-- This is essentially helloWorld2D
noisyCorr :: Model ('HPair 'HReal 'HReal) 'HUnit
noisyCorr = do_ [ x :<~ stdNormal
                , y :<~ Normal (Var x) (Real 1) ]
            (Dirac (Pair (Pair (Var x) (Var y)) Unit))
    where (x,y) = (V "x", V "y")

-- | Boolean example
----------------------------------------------------------------------
                    
burglarAlarm :: Model ('HEither 'HUnit 'HUnit)
                      ('HEither 'HUnit 'HUnit)
burglarAlarm = do_ [ b :<~ bern_ (Real 0.0001)
                   , a :<~ bern_ (If (Var b) (Real 0.95) (Real 0.01)) ]
                   (Dirac (Pair (Var a) (Var b)))
    where (a,b) = (V "a", V "b")

boolBase :: Base ('HEither 'HUnit 'HUnit)
boolBase = Either (Dirac_ Unit) (Dirac_ Unit)


diracPlus :: Model 'HReal 'HUnit
diracPlus = Do (x :<~ (Dirac (Real 5)))
               (Dirac (Pair (Add (Var x) (Var x)) Unit))
    where x = V "x"

twoDice :: Model 'HReal 'HReal
twoDice = do_ [ x :<~ msum_ [Dirac (Real 1), Dirac (Real 2), Dirac (Real 3)]
              , y :<~ msum_ [Dirac (Real 2), Dirac (Real 3), Dirac (Real 4)]
              , d :<~ bern_ (Real 0.5)
              , r :<~ Dirac (If (Var d) (Var x :: Term 'HReal) (Var y)) ]
          (Dirac (Pair (Var r) (Var d)))
    where (x,y,r,d) = (V "x", V "y", V "r", V "d")
                      

-- | Testing equality on Hakaru terms
----------------------------------------------------------------------
                  
eqTests :: Test
eqTests =
    TestList
    [
     "1+4 == 1+4" ~: termEq (Add (Real 1) (Real 4)) (Add (Real 1) (Real 4)) ~?= yes
    ,"1+4 == 4+1" ~: termEq (Add (Real 1) (Real 4)) (Add (Real 4) (Real 1)) ~?= yes
    ,"--1 =?= 1"  ~: termEq (Neg (Neg (Real 1))) (Real 1) ~?= unknown
    ,"4*3 == 2*6" ~: termEq (Mul (Real 4) (Real 3)) (Mul (Real 2) (Real 6)) ~?= yes
    , "-1 =/= --1" ~: termEq (Neg (Real 1)) (Neg (Real (-1))) ~?= no
    ]
