{-# LANGUAGE GADTs, DataKinds, FlexibleContexts #-}

module Simplify where

import Syntax
import Helpers

import Data.List (find)

monadRightId :: (Eq (Term a)) => Term ('HMeasure a) -> Term ('HMeasure a)
monadRightId p@(Do (v :<~ m) (Dirac e))
                       | Var v == e
                           = case jmEq (typeOf m) (typeOf (Dirac e)) of
                               Just Refl -> monadRightId m
                               Nothing   -> error $ "Could not apply monadRightId to " ++ show p
monadRightId (Do g m') = Do g $ monadRightId m'
monadRightId (MPlus m m') = MPlus (monadRightId m) (monadRightId m')
monadRightId p' = p'

mplusId :: Term ('HMeasure a) -> Term ('HMeasure a)
mplusId (MPlus m m') = mplus_ m m'
mplusId (Do (x :<~ m) m') = (Do (x :<~ mplusId m) $ mplusId m')
mplusId (Do g m) = (Do g $ mplusId m)
mplusId (Dirac (Total m)) = Dirac (Total $ mplusId m)
mplusId p = p

type Binding = (Var, Term 'HReal)    

-- | Unfinished / incorrect
dedupCond :: (Eq (Term a)) => Term a -> [Binding] -> CH (Term a, [Binding])
dedupCond p@(If (Less c c') e e') inputs = do  
  addVarsIn p
  case jmEq (typeOf e) TReal of
    Just Refl -> case (find ((==p).snd) inputs) of
                   Just (x,_) -> do (p',outs) <- dedupCond p []
                                    return (p', outs++[(x,p')])
                   Nothing    -> do xc' <- freshVar "sh"
                                    xe  <- freshVar "sh"
                                    xe' <- freshVar "sh"
                                    let inputs' = inputs ++
                                                  [(xc',c'), (xe,e), (xe',e')]
                                    (dc', outc') <- dedupCond c' inputs'
                                    (de,  oute)  <- dedupCond e  inputs'
                                    (de', oute') <- dedupCond e' inputs'
                                    return (If (Less c dc') e e',
                                            outc'++oute++oute')
    _ -> undefined

shareClamped :: (Eq (Term a))
             => Term a
             -> CH (Term a, [(Var, Term 'HReal)])
shareClamped p@(If (Less c c') e e') = do
  addVarsIn p
  (sh_c', lc') <- shareClamped c'
  (sh_e , le ) <- shareClamped e
  (sh_e', le') <- shareClamped e'
  let bindings = lc' ++ le ++ le'
  case jmEq (typeOf e) TReal of
    Just Refl | c' == e  -> do x <- freshVar "sh"                               
                               return ( If (Less c (Var x)) (Var x) sh_e'
                                      , (x, c') : bindings 
                                      )
    Just Refl | c' == e' -> do x <- freshVar "sh"
                               return ( If (Less c (Var x)) sh_e (Var x)
                                      , (x, c') : bindings
                                      )
    _                    -> return ( If (Less c sh_c') sh_e sh_e'
                                   , bindings
                                   )
shareClamped p = return (p, [])

shareClampedM :: (Eq (Term a)) => Term ('HMeasure a) -> CH (Term ('HMeasure a))
shareClampedM (Dirac e) = do (e', bindings) <- shareClamped e
                             let letbind (x,c) = LetInl x (Inl c :: Term ('HEither 'HReal 'HReal))
                             guards (map letbind bindings) (dirac e') 
                             -- case mvc of
                             --   Just (x,c) -> guard (LetInl x (Inl c :: Term ('HEither 'HReal 'HReal)))
                             --                       (dirac e')
                             --   Nothing    -> dirac e'
-- shareClampedM p@(Dirac (If (Less c c') e e')) = 
--                      case jmEq (typeOf e) TReal of
--                        Just Refl | c' == e  -> letinl (Inl c' :: Term ('HEither 'HReal 'HReal)) $ \x ->
--                                                dirac (If (Less c x) x e')
--                        Just Refl | c' == e' -> letinl (Inl c' :: Term ('HEither 'HReal 'HReal)) $ \x ->
--                                                dirac (If (Less c x) e x)
--                        Nothing -> return p
shareClampedM p@(Do (x :<~ m) m') = do
                       addVarsIn p
                       sm  <- shareClampedM m
                       sm' <- shareClampedM m'
                       return (Do (x :<~ sm) sm')
shareClampedM p@(Do g m) = addVarsIn p >> (guard g $ shareClampedM m)
shareClampedM p = return p
  

shareTest1 :: IO ()
shareTest1 = do
  let m = Do ((V "_") :<~ Dirac (Real 5))
             (Dirac (If (Less (Real 1) (normalDensity (Real 0) (Real 1) (Real 0)))
                        (normalDensity (Real 0) (Real 1) (Real 0))
                        (Real 1)))
  print m
  putStrLn "------------"
  print $ evalNames (shareClampedM m)


shareTest2 :: IO ()
shareTest2 = do
  let e = normalDensity (Real 0) (Real 1) (Real 0)
      m = do_ [ (V "_") :<~ Dirac Unit
              , (V "_") :<~ Dirac Unit ]
              (Dirac (If (Less (Real 42)
                               (If (Less (Real 0) e) (Real 0) e))
                         (Real 37)
                         e))
  print m
  putStrLn "------------"
  print $ evalNames (shareClampedM m)
             
