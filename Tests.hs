{-# LANGUAGE DataKinds #-}

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

infer :: (Sing a, Sing b, Inferrable a) => Term ('HMeasure ('HPair a b)) -> IO ()
infer prog = let (b,t)  = (fst (base 0) [], Var obs)
                 anss   = disintegrate prog b t
                 initState e = (Names 0 (varsIn e), [])
                 sat (e,cs) = (e, evalState (mapM solve cs) (initState e))
                 inferred = fmap (second (findBase b . group) . sat) anss
             in putStrLn $ format (title prog b t) inferred

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

helloWorld2D :: Model ('HPair 'HReal 'HReal) 'HReal
helloWorld2D = do_ [ mu :<~ stdNormal
                   , x  :<~ Normal (Var mu) (Real 1)
                   , y  :<~ Normal (Var mu) (Real 1) ]
                   (Dirac (Pair (Pair (Var x) (Var y)) (Var mu)))
    where (mu, x, y) = (V "mu", V "x", V "y")

unclampedGPA :: Model 'HReal ('HEither 'HUnit 'HUnit)
unclampedGPA = MPlus (Do (x :<~ Normal (Real 2) (Real 3))
                         (Dirac (Pair (Var x) true_)))
                     (Do (y :<~ Normal (Real 5) (Real 6))
                         (Dirac (Pair (Var y) false_)))
    where (x,y) = (V "x", V "y")

-- | Examples that produce base-constraints containing term-language variables
-------------------------------------------------------------------------------
lubAndMPlus :: Model 'HReal 'HUnit
lubAndMPlus = do_ [ x  :<~ stdNormal
                  , y :<~ MPlus (Normal (Var x) (Real 1))
                                (Dirac (Real 0)) ]
             (Dirac (Pair (Add (Var x) (Var y)) Unit))
    where (x,y) = (V "x", V "y")

addAdd :: Model 'HReal 'HUnit
addAdd = do_ [ x :<~ stdNormal
             , y :<~ stdNormal ]
         (Dirac (Pair (Add (Var y) (Add (Var x) (Var x))) Unit))
    where (x,y) = (V "x", V "y")
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

sqrNorm :: Model 'HReal 'HUnit
sqrNorm = Do (n :<~ Normal (Sqrt (Real 2.6)) (Sqrt (Real 0.1)))
             (Dirac (Pair (Square (Var n)) Unit))
    where n = V "n"

eitherTest :: Model ('HEither 'HUnit 'HUnit) 'HUnit
eitherTest = Dirac (Pair (Inl Unit) Unit)

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

proposal1 :: Model ('HPair 'HReal 'HReal) 'HUnit
proposal1 = do_ [ x :<~ stdNormal
                , y :<~ MPlus (Normal (Var x) (Real 0.1))
                              (Dirac (Var x)) ]
            (Dirac (Pair (Pair (Var x) (Var y)) Unit))
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
                             , a' :<~ Normal (Var a) (Real 0.1) ]
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
