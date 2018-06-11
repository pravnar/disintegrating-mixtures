{-# LANGUAGE DataKinds, GADTs #-}

module Tests where

import Syntax
import Pretty
import Helpers    
import Disintegrate
import Control.Monad.State
-- import           Data.List (groupBy)
import           Text.PrettyPrint hiding (parens)
import qualified Text.PrettyPrint as PP (parens)
import System.Process (callCommand)
import Test.HUnit
-- import           Debug.Trace

obs :: Var
obs = V "t"

title :: Term ('HMeasure ('HPair a b)) -> Base a -> Term a -> Doc
title prog base t = text "disintegrate" <+> (PP.parens (pretty prog) $$
                                             PP.parens (pretty base) $$
                                             PP.parens (pretty obs))

format :: (Displayable a b) => Doc -> Trace (a, b) -> String
format call anss = render $ space $$ call $$ text "==>"
                   $+$ pretty (display anss) $+$ text (replicate 80 '-')

check :: (Sing a, Sing b) => Term ('HMeasure ('HPair a b)) -> Base a -> IO ()
check prog base = putStrLn $ format (title prog base t) (disintegrate prog base t)
    where t = Var obs

constraintsOn :: (Sing a, Sing b, Inferrable a) => Term ('HMeasure ('HPair a b)) -> IO ()
constraintsOn prog = print (fmap snd $ disintegrate prog b t)
    where (b,t) = (fst (base 0) [], Var obs)

infer :: (Sing a, Sing b, Inferrable a) => Term ('HMeasure ('HPair a b)) -> Term a -> Trace (Term ('HMeasure b), Base a)
infer prog t = let b      = fst (base 0) []
                   anss   = disintegrate prog b t
                   initState e = (Names 0 (varsIn e), [])
                   sat (e,cs) = (e, evalState (mapM solve cs) (initState e))
                   inferred = fmap (second (findBase b . group) . sat) anss
             in inferred

printInferred :: (Sing a, Sing b, Inferrable a) => Term ('HMeasure ('HPair a b)) -> IO ()
printInferred prog = let (b,t)  = (fst (base 0) [], Var obs)
                     in putStrLn $ format (title prog b t) (infer prog t)

-- | Draw a graph of the disintegration trace and save it in a pdf file
viz :: (Sing a, Sing b) => FilePath -> Term ('HMeasure ('HPair a b)) -> Base a -> IO ()
viz file prog base
    = do let t       = Var obs
             out     = display (disintegrate prog base t)
             dir     = "./plots/"
             dotFile = dir++file++".dot"
             pdfFile = dir++file++".pdf"
         writeFile dotFile (traceToDot (title prog base t) out)
         callCommand $ "dot -Tpdf " ++ dotFile ++ " > " ++ pdfFile

type Model a b = Term ('HMeasure ('HPair a b))

stdNormal :: Term ('HMeasure 'HReal)
stdNormal = Normal (Real 0) (Real 1)

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

-- | MCMC
--------------------------------------------------------------------------------

fromTrace :: Trace a -> Maybe a
fromTrace Bot        = Nothing
fromTrace (Return a) = Just a
fromTrace (Step _ t) = fromTrace t
fromTrace (Lub t t') = case fromTrace t of
                         Just a  -> Just a
                         Nothing -> fromTrace t'

choosePosterior :: (Term a -> Trace (Term ('HMeasure b), c)) -> Term a -> Maybe (Term ('HMeasure b))
choosePosterior tracekern t = fromTrace (tracekern t) >>= return . fst

principalBase :: (Sing a, Sing b, Inferrable a)
              => Term ('HMeasure ('HPair a b)) -> Term a -> Maybe (Base a)
principalBase m t = fromTrace (infer m t) >>= return . snd

allBases :: (Sing a, Sing b, Inferrable a)
         => Term ('HMeasure ('HPair a b)) -> Term a -> Trace (Base a)
allBases m t = fmap snd $ infer m t

switch :: (Sing a, Sing b) => Term ('HPair a b) -> Term ('HPair b a)
switch p = Pair (scnd p) (frst p)

bplusExt :: (Sing a) => Base a -> Base a -> Base a
bplusExt b b' = case (typeOf_ b) of
                  TReal -> bplus b b'
                  _ -> ext b b'
    where ext (Dirac_ Unit)  (Dirac_ Unit)  = Dirac_ Unit
          ext (Either l1 r1) (Either l2 r2) = Either (bplusExt l1 l2) (bplusExt r1 r2)
          ext (Bindx  b1 f1) (Bindx  b2 f2) = Bindx  (bplusExt b1 b2) (\x -> bplusExt (f1 x) (f2 x))
          ext (Error_ e1)    (Error_ e2)    = Error_ (e1 ++ " and " ++ e2)
          ext _ _ = Error_ $ "bplusExt: trying to add " ++ show b ++ " and " ++ show b'

type Ratio = (Term ('HMeasure 'HUnit), Term ('HMeasure 'HUnit))

    

pairWithUnit :: (Sing a) => Term ('HMeasure a) -> N (Term ('HMeasure ('HPair a 'HUnit)))
pairWithUnit = liftMeasure (\x -> Pair x Unit)

density :: (Sing a, Inferrable a)
        => Term ('HMeasure a) -> Term ('HMeasure a) -> Term a -> Maybe Ratio
density m n t = do let (m',n') = withDiffNames (pairWithUnit m) (pairWithUnit n)
                   bm <- principalBase m' t
                   bn <- principalBase n' t
                   let b = bplusExt bm bn                       
                   d1 <- choosePosterior (disintegrate m' b) t
                   d2 <- choosePosterior (disintegrate n' b) t
                   return (d1,d2)

greensRatio :: (Sing b, Inferrable b)
            => Term ('HMeasure b)
            -> (Term b -> Term ('HMeasure b))
            -> Term ('HPair b b)
            -> Maybe Ratio
greensRatio target proposal = let (m,mrev) = evalNames $
                                             do m    <- bindx target proposal
                                                mrev <- liftMeasure switch m
                                                return (m,mrev)
                              in density mrev m

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

revJumpProposal :: Model ('HPair ('HEither 'HReal ('HPair 'HReal 'HReal))
                                 ('HEither 'HReal ('HPair 'HReal 'HReal)))
                         'HUnit
revJumpProposal = MPlus (do_ [ a  :<~ stdNormal
                             , b  :<~ stdNormal
                             -- , a' :<~ Dirac (Var a :: Term 'HReal) 
                             , a' :<~ Normal (Var a) (Real 0.1)
                             ]
                             (Dirac (Pair (Pair (Inr (Pair (Var a) (Var b)))
                                                (Inl (Var a')))
                                          Unit)))
                        (do_ [ x  :<~ stdNormal
                             , x' :<~ Normal (Var x) (Real 0.1)
                             , y  :<~ Normal (Var x) (Real 0.1) ]
                             (Dirac (Pair (Pair (Inl (Var x))
                                                (Inr (Pair (Var x') (Var y))))
                                          Unit)))
    where (a,b,a',x,x',y) = (V "a", V "b", V "a'", V "x", V "x'", V "y")

revJumpBase :: Base ('HPair ('HEither 'HReal ('HPair 'HReal 'HReal))
                            ('HEither 'HReal ('HPair 'HReal 'HReal)))
revJumpBase = Bindx (Either Lebesgue_ (Bindx Lebesgue_ (const Lebesgue_))) $
              \x -> (Either Lebesgue_ (Bindx Lebesgue_ (const Lebesgue_)))

either_ :: (Sing a, Sing b) => Term a -> Term b -> Term ('HMeasure ('HEither a b))
either_ a b = MPlus (Dirac (Inl a)) (Dirac (Inr b))
          

dimensionMatch :: Model 'HReal ('HEither 'HReal ('HPair 'HReal 'HReal))
dimensionMatch = do_ [ x :<~ stdNormal
                     , y :<~ stdNormal
                     , z :<~ either_ (Var x :: Term 'HReal)
                                     (Pair (Var x) (Var y) :: Term ('HPair 'HReal 'HReal)) ]
                     (Dirac (Pair (Add (Var x) (Var y))
                                  (Var z)))
    where (x,y,z) = (V "xen", V "yen", V "zen")

dimMatchTarget :: Term ('HMeasure ('HEither 'HReal ('HPair 'HReal 'HReal)))
dimMatchTarget = let p = choosePosterior (disintegrate dimensionMatch Lebesgue_) (Real 42)
                 in case p of
                      Just t  -> t
                      Nothing -> error "dimMatchTarget: got nothing"

dimMatchProposal :: Term ('HEither 'HReal ('HPair 'HReal 'HReal))
                 -> Term ('HMeasure ('HEither 'HReal ('HPair 'HReal 'HReal)))
dimMatchProposal e = MPlus (do_ [ LetInl x e
                                , u :<~ stdNormal
                                , u2 :<~ stdNormal ]
                                (Dirac (Inr (Pair -- (Add   (Var x) (Var u))
                                                  -- (minus (Var x) (Var u2))
                                                  (Var x) (Var u)
                                            ))))
                           (do_ [ LetInr x e
                                , u :<~ Normal (frac (Add (frst (Var x :: Term ('HPair 'HReal 'HReal)))
                                                          (scnd (Var x :: Term ('HPair 'HReal 'HReal))))
                                                     (Real 2))
                                               (Real 0.0001) ]
                                (Dirac (Inl (Var u))))
    where (x,u,u2) = (V "box", V "bucks", V "verysafe")

dim     = evalNames (bindx dimMatchTarget dimMatchProposal)
dimrev  = evalNames (liftMeasure switch dim)
udim    = evalNames (pairWithUnit dim)
udimrev = evalNames (pairWithUnit dimrev)
         
                     
type NParamsType = 'HPair 'HReal 'HReal
type OneNormal  = NParamsType
type TwoNormals = 'HPair NParamsType NParamsType

finiteMixtureModel :: Model 'HReal ('HEither OneNormal TwoNormals)
finiteMixtureModel = MPlus (do_ [ m1 :<~ stdNormal
                                , s1 :<~ stdNormal
                                , x :<~ Normal (Var m1) (Var s1) ]
                                (Dirac (Pair (Var x) (Inl (Pair (Var m1) (Var s1))))))
                           (do_ [ m1 :<~ stdNormal
                                , s1 :<~ stdNormal
                                , m2 :<~ stdNormal
                                , s2 :<~ stdNormal
                                , x :<~ MPlus (Normal (Var m1) (Var s1))
                                              (Normal (Var m2) (Var s2)) ]
                                (Dirac (Pair (Var x) (Inr (Pair (Pair (Var m1) (Var s1))
                                                                (Pair (Var m2) (Var s2)))))))
    where (m1,s1,m2,s2,x) = (V "m1", V "s1", V "m2", V "s2", V "x")                            

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

bern_ :: Term 'HReal -> Term ('HMeasure ('HEither 'HUnit 'HUnit))
bern_ p = MPlus (Do (Factor p) (Dirac true_))
                (Do (Factor (minus (Real 1) p)) (Dirac false_))
                    
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

-- | Mutual information
-- https://papers.nips.cc/paper/7180-estimating-mutual-information-for-discrete-continuous-mixtures
----------------------------------------------------------------------------------------------------

-- Experiment I from the paper
gao :: N (Term ('HMeasure ('HPair 'HReal 'HReal)))
gao = do pm <- productM stdNormal stdNormal
         return $ msum_ [ pm
                        , weight (Real 0.45) (Dirac (Pair (Real    1) (Real    1)))
                        , weight (Real 0.45) (Dirac (Pair (Real $ -1) (Real $ -1)))
                        , weight (Real 0.05) (Dirac (Pair (Real    1) (Real $ -1)))
                        , weight (Real 0.05) (Dirac (Pair (Real $ -1) (Real    1)))]

gaoTwo :: N (Term ('HMeasure ('HPair 'HReal 'HReal)))
gaoTwo = do pm <- productM stdNormal stdNormal
            return $ msum_ [ pm
                           , weight (Real 0.55) (Dirac (Pair (Real    1) (Real    1)))
                           , weight (Real 0.45) (Dirac (Pair (Real $ -1) (Real    1)))]
         

fstmarginal :: (Sing a, Sing b) => Term ('HMeasure ('HPair a b)) -> N (Term ('HMeasure a))
fstmarginal = liftMeasure Fst

sndmarginal :: (Sing a, Sing b) => Term ('HMeasure ('HPair a b)) -> N (Term ('HMeasure b))
sndmarginal = liftMeasure Snd

-- The Radon-Nikodym derivative term used in the definition of mutual
-- information in Gao et el.
densMI :: (Sing a, Sing b, Inferrable a, Inferrable b)
       => N (Term ('HMeasure ('HPair a b)))
       -> Term ('HPair a b)
       -> Maybe Ratio
densMI nm = let (mu,nu) = evalNames (do mu <- nm
                                        addVarsIn mu
                                        mf <- nm >>= fstmarginal
                                        ms <- nm >>= sndmarginal
                                        nu <- productM mf ms
                                        return (mu,nu))
            in density mu nu

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
