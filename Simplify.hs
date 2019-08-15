{-# LANGUAGE GADTs, DataKinds, FlexibleContexts #-}

module Simplify where

import Syntax
import Helpers

monadRightId :: (Eq (Term a)) => Term ('HMeasure a) -> Term ('HMeasure a)
monadRightId p@(Do (v :<~ m) (Dirac e)) | Var v == e
                       = case jmEq (typeOf m) (typeOf (Dirac e)) of
                           Just Refl -> monadRightId m
                           Nothing   -> error $ "Could not apply monadRightId to " ++ show p
monadRightId (Do g m') = Do g $ monadRightId m'
monadRightId p' = p'
                                                     
