{-# LANGUAGE DataKinds,
             TypeOperators #-}

module MutualInfo where

import Syntax
import Helpers
import UserInterface
import Hakaru

import qualified Language.Hakaru.Simplify as S
import qualified Language.Hakaru.Expect as E
import qualified Language.Hakaru.Sample as Sam
import qualified Language.Hakaru.Pretty.Concrete as PC
import qualified Language.Hakaru.Syntax.Prelude as HP
import qualified Language.Hakaru.Syntax.AST as AST
import qualified Language.Hakaru.Syntax.ABT as ABT
import qualified Language.Hakaru.Types.Sing as TS
import qualified Language.Hakaru.Types.DataKind as DK
import qualified Language.Hakaru.Syntax.Variable as SV
import qualified Data.Text as Text
import qualified Control.Monad.State as MS
    
    
-- | Mutual information
-- https://papers.nips.cc/paper/7180-estimating-mutual-information-for-discrete-continuous-mixtures
----------------------------------------------------------------------------------------------------

-- Experiment I from the paper
gao :: CH (Term ('HMeasure ('HPair 'HReal 'HReal)))
gao = do pm <- productM stdNormal stdNormal
         return $ msum_ [ pm
                        , weight (Real 0.45) (Dirac (Pair (Real    1) (Real    1)))
                        , weight (Real 0.45) (Dirac (Pair (Real $ -1) (Real $ -1)))
                        , weight (Real 0.05) (Dirac (Pair (Real    1) (Real $ -1)))
                        , weight (Real 0.05) (Dirac (Pair (Real $ -1) (Real    1)))]
         
fstmarginal :: (Sing a, Sing b) => Term ('HMeasure ('HPair a b)) -> CH (Term ('HMeasure a))
fstmarginal = liftMeasure Fst

sndmarginal :: (Sing a, Sing b) => Term ('HMeasure ('HPair a b)) -> CH (Term ('HMeasure b))
sndmarginal = liftMeasure Snd

-- The Radon-Nikodym derivative term used in the definition of mutual
-- information in Gao et el.
densMI :: (Sing a, Sing b, Inferrable a, Inferrable b)
       => CH (Term ('HMeasure ('HPair a b)))
       -> Term ('HPair a b)
       -> Maybe Ratio
densMI nm = let (mu,nu) = evalNames (do mu <- nm
                                        addVarsIn mu
                                        mf <- nm >>= fstmarginal
                                        ms <- nm >>= sndmarginal
                                        nu <- productM mf ms
                                        return (mu,nu))
            in density mu nu

-- | Here we convert from core Hakaru to (mainline) Hakaru
-- to experiment with applying algebraic simplifications provided by
-- the mainline system
test1 :: IO ()
test1 = do let nm = "t"
               obs = V nm
               Just (num,denom) = densMI gao (Var obs)
               numH = toHakaruLam (TS.sPair TS.SReal TS.SReal) nm num
               denH = toHakaruLam (TS.sPair TS.SReal TS.SReal) nm denom
               one = HP.literal_ $ AST.LReal 1
               two = HP.literal_ $ AST.LReal 2
               three = HP.literal_ $ AST.LReal 3
               app11 = \e -> HP.app e (HP.pair one one)
               app21 = \e -> HP.app e (HP.pair two one)
               app22 = \e -> HP.app e (HP.pair two two)
               app23 = \e -> HP.app e (HP.pair two three)
               app33 = \e -> HP.app e (HP.pair three three)
           -- numSimpl <- S.simplifyDebug False 30 numH
           -- print $ PC.pretty numSimpl
           let numTotal = E.total $ app33 numH -- calculate the total
                                               -- mass of a measure
                                               -- (using integration)
               denTotal = E.total $ app33 denH
           print $ PC.pretty numTotal
           putStrLn "---------------"
           print $ PC.pretty denTotal           
           numTotalSimpl <- S.simplifyDebug False 30 numTotal
           denTotalSimpl <- S.simplifyDebug False 30 denTotal
           print $ PC.pretty numTotalSimpl
           print $ PC.pretty denTotalSimpl
           print $ Sam.runEvaluate (numTotalSimpl HP./ denTotalSimpl)

test2 :: IO ()
test2 = do let nm = "t"
               obs = V nm
               Just (num,denom) = densMI gao (Var obs)
               numH = toHakaruLam (TS.sPair TS.SReal TS.SReal) nm num
               denH = toHakaruLam (TS.sPair TS.SReal TS.SReal) nm denom
               r = 5
               points = [(x,y) | x <- [-r..r], y <- [-r..r]]
               toLit = HP.literal_ . AST.LReal
               appXYs = map (\(x,y) -> \e -> HP.app e $ HP.pair (toLit x) (toLit y)) points
               numTotals = map (\f -> E.total $ f numH) appXYs
               denTotals = map (\f -> E.total $ f denH) appXYs
           numTotalSimpls <- mapM (S.simplifyDebug False 30) numTotals
           denTotalSimpls <- mapM (S.simplifyDebug False 30) denTotals
           let ratios = map (\(n,d) -> Sam.runEvaluate (n HP./ d)) $ zip numTotalSimpls denTotalSimpls
           print $ zip (map (\(x,y) -> (fromRational x, fromRational y)) points) ratios
