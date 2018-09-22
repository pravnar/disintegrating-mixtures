{-# LANGUAGE DataKinds, GADTs #-}

module UserInterface where

import Syntax
import Pretty
import Helpers
import Disintegrate

import Control.Monad.State
import           Text.PrettyPrint hiding (parens)
import qualified Text.PrettyPrint as PP (parens)
import System.Process (callCommand)


-- | Visualizing all outputs of disintegration
----------------------------------------------------------------------
    
-- | Print (all of) the output(s) of base-checking disintegration
check :: (Sing a, Sing b) => Term ('HMeasure ('HPair a b)) -> Base a -> IO ()
check prog base = putStrLn $ format (title prog base t) (disintegrate prog base t)
    where t = Var obs

-- | Print (all of) the output(s) of base inference
infer :: (Sing a, Sing b, Inferrable a) => Term ('HMeasure ('HPair a b)) -> Term a -> Trace (Term ('HMeasure b), Base a)
infer prog t = let b      = fst (base 0) []
                   anss   = disintegrate prog b t
                   initState e = (Names 0 (varsIn e), [])
                   sat (e,cs) = (e, evalState (mapM solve cs) (initState e))
                   inferred = fmap (second (findBase b . group) . sat) anss
             in inferred
                

-- | Obtaining the results of disintegration
----------------------------------------------------------------------

-- | Obtain a single conditional dist. (left-most in the disintegration trace)
condition :: (Sing a, Sing b)
          => Term ('HMeasure ('HPair a b))
          -> Base a
          -> Term a
          -> Maybe (Term ('HMeasure b))
condition m b = choosePosterior (disintegrate m b)

-- | Infer a single base measure (left-most in the disintegration trace) 
principalBase :: (Sing a, Sing b, Inferrable a)
              => Term ('HMeasure ('HPair a b)) -> Term a -> Maybe (Base a)
principalBase m t = fromTrace (infer m t) >>= return . snd

-- | Get all the inferred bases as a Trace
allBases :: (Sing a, Sing b, Inferrable a)
         => Term ('HMeasure ('HPair a b)) -> Term a -> Trace (Base a)
allBases m t = fmap snd $ infer m t

fromTrace :: Trace a -> Maybe a
fromTrace Bot        = Nothing
fromTrace (Return a) = Just a
fromTrace (Step _ t) = fromTrace t
fromTrace (Lub t t') = case fromTrace t of
                         Just a  -> Just a
                         Nothing -> fromTrace t'

choosePosterior :: (Term a -> Trace (Term ('HMeasure b), c)) -> Term a -> Maybe (Term ('HMeasure b))
choosePosterior tracekern t = fromTrace (tracekern t) >>= return . fst
                              

-- | Unrestricted density calculator
----------------------------------------------------------------------
-- Here the base measure (i.e., the second argument to density) can be
-- a core Hakaru measure (i.e., not restricted to Base)

density :: (Sing a, Inferrable a)
        => Term ('HMeasure a) -> Term ('HMeasure a) -> Term a -> Maybe Ratio
density m n t = do let (m',n') = withDiffNames (pairWithUnit m) (pairWithUnit n)
                   bm <- principalBase m' t
                   bn <- principalBase n' t
                   let b = bplusExt bm bn                       
                   d1 <- choosePosterior (disintegrate m' b) t
                   d2 <- choosePosterior (disintegrate n' b) t
                   return (d1,d2)
                              
type Ratio = (Term ('HMeasure 'HUnit), Term ('HMeasure 'HUnit))

bplusExt :: (Sing a) => Base a -> Base a -> Base a
bplusExt b b' = case (typeOf_ b) of
                  TReal -> bplus b b'
                  _ -> ext b b'
    where ext (Dirac_ Unit)  (Dirac_ Unit)  = Dirac_ Unit
          ext (Either l1 r1) (Either l2 r2) = Either (bplusExt l1 l2) (bplusExt r1 r2)
          ext (Bindx  b1 f1) (Bindx  b2 f2) = Bindx  (bplusExt b1 b2) (\x -> bplusExt (f1 x) (f2 x))
          ext (Error_ e1)    (Error_ e2)    = Error_ (e1 ++ " and " ++ e2)
          ext _ _ = Error_ $ "bplusExt: trying to add " ++ show b ++ " and " ++ show b'


-- | Importance sampling using unrestricted density calculation
----------------------------------------------------------------------

ratio2Real :: Ratio -> Term 'HReal
ratio2Real (n,d) = Total n `Helpers.div` Total d

importance :: (Sing a, Inferrable a)
           => Term ('HMeasure a)
           -> Term ('HMeasure a)
           -> CH (Term ('HMeasure ('HPair a 'HReal)))
importance target proposal =
    bind proposal $ \x ->
    case density target proposal x of
      Just r  -> dirac $ Pair x (ratio2Real r)
      Nothing -> error "importance: density failed"
                    
                    
-- | Metropolis-Hastings-Green kernel for MCMC sampling
----------------------------------------------------------------------

mhg :: (Sing b, Inferrable b)
    => Term ('HMeasure b)
    -> (Term b -> CH (Term ('HMeasure b)))
    -> Term b
    -> CH (Term ('HMeasure b))
mhg target propK p =
      do proposal <- propK p
         unif <- stdUniform
         bind proposal $ \q ->
             case greensRatio target propK (Pair p q) of
               Just r -> bind unif $ \u ->
                         dirac $ if_ (less u (min_ (Real 1) (ratio2Real r))) q p
               Nothing    -> error "mhg: greensRatio failed"

-- | Use unrestricted density to calculate MHG acceptance ratio
greensRatio :: (Sing b, Inferrable b)
            => Term ('HMeasure b)
            -> (Term b -> CH (Term ('HMeasure b)))
            -> Term ('HPair b b)
            -> Maybe Ratio
greensRatio target proposal = let (m,mrev) = evalNames $
                                             do m    <- bindx target proposal
                                                mrev <- liftMeasure switch m
                                                return (m,mrev)
                              in density mrev m

switch :: (Sing a, Sing b) => Term ('HPair a b) -> Term ('HPair b a)
switch p = Pair (scnd p) (frst p)


-- | Helpers for visualizing disintegration results
----------------------------------------------------------------------
              
obs :: Var
obs = V "t"

title :: Term ('HMeasure ('HPair a b)) -> Base a -> Term a -> Doc
title prog base t = text "disintegrate" <+> (PP.parens (pretty prog) $$
                                             PP.parens (pretty base) $$
                                             PP.parens (pretty obs))

format :: (Displayable a b) => Doc -> Trace (a, b) -> String
format call anss = render $ space $$ call $$ text "==>"
                   $+$ pretty (display anss) $+$ text (replicate 80 '-')

constraintsOn :: (Sing a, Sing b, Inferrable a) => Term ('HMeasure ('HPair a b)) -> Term a -> IO ()
constraintsOn prog t = print (fmap snd $ disintegrate prog b t)
    where b = fst (base 0) []

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
