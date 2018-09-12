{-# LANGUAGE DataKinds #-}

module RevJump where    

import Syntax
import Helpers
import Disintegrate    
import Tests

    
-- | Reversible jump MCMC
--------------------------------------------------------------------------------

-- What works (June 12 2018):

-- greensRatio revJumpTarget revJumpProposal
-- greensRatio dimMatchTarget revJumpProposal

-- What doesn't work (June 12 2018):
-- greensRatio dimMatchTarget dimMatchProposal
                     

-- An example measure that we might find in the denominator of acceptance ratio
-- That is, an example of a bindx target proposal for some target and some proposal
revJumpDenom :: Model ('HPair ('HEither 'HReal ('HPair 'HReal 'HReal))
                                 ('HEither 'HReal ('HPair 'HReal 'HReal)))
                         'HUnit
revJumpDenom = MPlus (do_ [ a  :<~ stdNormal
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

-- This works currently (June 12 2018)
-- let rswap = evalNames $ liftMeasure Fst revJumpNumer >>= \p -> liftMeasure switch p >>= \p' -> pairWithUnit p'
-- allBases rswap (Var obs)

type R2 = 'HPair 'HReal 'HReal
type RPlusR2 = 'HEither 'HReal R2

-- | This is the same as calling bindx revJumpTarget revJumpProposal
-- (minimum working example)
revJumpMWE :: Term ('HMeasure ('HPair RPlusR2 RPlusR2))
revJumpMWE = Do (init :<~ MPlus (Do (a :<~ stdNormal) (Dirac (Inl (Var a :: Term 'HReal))))
                                (do_ [ b :<~ stdNormal
                                     , c :<~ stdNormal ]
                                     (Dirac (Inr (Pair (Var b :: Term 'HReal) (Var c :: Term 'HReal))))))
                       -- either_ (Real 5) (Pair (Real 42) (Real 43)))
                (MPlus (do_ [ LetInl x (Var init :: Term RPlusR2)
                            , x1 :<~ Normal (Var x) (Real 0.1)
                            , x2 :<~ Normal (Var x) (Real 0.1) ]
                            (Dirac (Pair (Var init) (Inr (Pair (Var x1) (Var x2))))))
                       (do_ [ LetInr xy (Var init :: Term RPlusR2)
                            , xy' :<~ Normal (Add (frst (Var xy :: Term R2))
                                                  (scnd (Var xy :: Term R2)))
                                             (Real 0.1) ]
                            (Dirac (Pair (Var init) (Inl (Var xy'))))))
    where (init,x,x1,x2,xy,xy',a,b,c) = (V "init", V "x", V "x1", V "x2", V "xy", V "xy'", V "a", V "b", V "c")

revJumpTarget :: Term ('HMeasure RPlusR2)
revJumpTarget = MPlus (Do (a :<~ stdNormal) (Dirac (Inl (Var a :: Term 'HReal))))
                          (do_ [ b :<~ stdNormal
                               , c :<~ stdNormal ]
                               (Dirac (Inr (Pair (Var b :: Term 'HReal) (Var c :: Term 'HReal)))))
    where (a,b,c) = (V "a", V "b", V "c")

revJumpProposal :: Term RPlusR2 -> Term ('HMeasure RPlusR2)
revJumpProposal e = MPlus (do_ [ LetInl x e
                               , x1 :<~ Normal (Var x) (Real 0.1)
                               , x2 :<~ Normal (Var x) (Real 0.1) ]
                               (Dirac  (Inr (Pair (Var x1) (Var x2)))))
                          (do_ [ LetInr xy e
                               , xy' :<~ Normal (Add (frst (Var xy :: Term R2))
                                                     (scnd (Var xy :: Term R2)))
                                                (Real 0.1) ]
                               (Dirac (Inl (Var xy'))))
    where (x,x1,x2,xy,xy') = (V "x", V "x1", V "x2", V "xy", V "xy'")

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

-- Based on Ken's idea: make the target have a density wrt the /usual/
-- base measure, aka lebesgue on all leaves (eg. either lebesgue
-- (bindx lebesgue (const lebesgue)))
dimMatch :: Model 'HReal ('HEither 'HReal ('HPair 'HReal 'HReal))
dimMatch = Do (init :<~ Normal (Real 0) (Real 10))
              (MPlus (Do (y :<~ Normal (Var init) (Real 0.1))
                         (Dirac (Pair (Var y) (Inl (Var init)))))
                     (do_ [ next :<~ Normal (Var init) (Real 1)
                          , y :<~ Normal (Var next) (Real 0.1) ]
                          (Dirac (Pair (Var y) (Inr (Pair (Var init) (Var next)))))))
    where (init, next, y) = (V "init", V "next", V "dimobs")

dimMatchTarget :: Term ('HMeasure ('HEither 'HReal ('HPair 'HReal 'HReal)))
dimMatchTarget = let p = choosePosterior (disintegrate dimMatch Lebesgue_) (Real 42)
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

-----------------------------------------------------------------------------------------------------
