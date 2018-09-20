{-# LANGUAGE DataKinds,
             TypeOperators #-}

module MutualInfo where

import Syntax
import Helpers
import Tests
import Hakaru

import qualified Language.Hakaru.Simplify as S
import qualified Language.Hakaru.Expect as E
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

test1 :: IO ()
test1 = do let Just (num,denom) = densMI gao (Var obs)
               numH = toHakaruLam (TS.sPair TS.SReal TS.SReal) num
               denH = toHakaruLam (TS.sPair TS.SReal TS.SReal) denom
               one = HP.literal_ $ AST.LReal 1
               app11 = \e -> HP.app e (HP.pair one one)
           -- numSimpl <- S.simplifyDebug False 30 numH
           -- print $ PC.pretty numSimpl
           let numTotal = E.total $ app11 numH
               denTotal = E.total $ app11 denH
           numTotalSimpl <- S.simplifyDebug False 30 numTotal
           denTotalSimpl <- S.simplifyDebug False 30 denTotal
           print $ PC.pretty numTotalSimpl
           print $ PC.pretty denTotalSimpl
