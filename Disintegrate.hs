{-# LANGUAGE GADTs, 
             DataKinds, 
             RankNTypes, 
             MultiParamTypeClasses,
             FlexibleInstances #-}

module Disintegrate where

import Syntax
import Pretty
import Helpers    
import Control.Monad (liftM2, forM)
import Data.Maybe (isNothing)
import Unsafe.Coerce (unsafeCoerce)

disintegrate :: (Sing a, Sing b)
             => Term ('HMeasure ('HPair a b))
             -> Base a
             -> Term a
             -> Trace (Term ('HMeasure b), [Constraint])
disintegrate term base obs = fmap output go
    where output (e,s) = (e , constraints s)
          go           = runDisintegrate transformer (initEnv term)
          transformer  = perform term k []
          k p          = constrainValue (frst p) base obs (wrap (scnd p))
          wrap e h     = return $ wrapHeap h (Dirac e)

-- | Divide a base against another at a given point
-- Failure (repr. with bot) means that base1 does not have a density
-- wrt base2
-- Success is a set of conditions (repr. as a sequence of
-- guards) under which a density exists

-- divide :: (Sing a) => Base a -> Base a -> Term a -> D [Guard Var]
divide :: Base 'HReal -> Base 'HReal -> Term 'HReal -> D [Guard Var]
divide (Dirac_ e)       (Dirac_ e')       _ = ifYesElse (return []) bot (termEq e e')
divide (Dirac_ _)       Lebesgue_         _ = bot
divide Lebesgue_        (Dirac_ _)        _ = bot
divide Lebesgue_        Lebesgue_         _ = return []
-- divide (Either b b')    (Either c c')     t = liftM2 gplus left right
--     where x     = V "x"
--           left  = (LetInl x t :) <$> divide b  c  (Var x)
--           right = (LetInr x t :) <$> divide b' c' (Var x) 
-- divide (Bindx b1 f1)    (Bindx b2 f2)     t = divide b1 b2 (frst t) >>= \gs ->
--                                               (gs ++) <$> divide (f1 $ frst t)
--                                                                  (f2 $ frst t)
--                                                                  (scnd t)
divide Lebesgue_        (Mixture False _) _ = bot
divide Lebesgue_        (Mixture True es) t = return [observeNot (Equal t e) | e <- es]
divide (Dirac_ e)       (Mixture _ es)    t =
    if k == 0 || any isNothing eqs
    then bot
    else return [Factor (Recip (Real k)), observe (Equal t e)]
    where eqs = map (termEq e) es
          k   = sum $ map (ifYesElse 1 0) eqs
divide (Mixture leb es) b t
    | leb       = gsum <$> liftM2 (:) (divide Lebesgue_ b t) gsM
    | otherwise = gsum <$> gsM
    where gsM = forM es (\e -> divide (Dirac_ e) b t)
divide b1 (LiftB f b2) t = (Factor (Recip (Jacobian f b2 y `Mul` g1 t)) :) <$>
                           divide b1' b2 y
    where ((b1', g1), y) = (liftB (invert f) b1, f @@ t)
divide b b' t = record (b :<: b') >> return [Divide b b' t]
                -- ^ Record the constraint that b must have a density wrt b'

liftB :: Invertible
      -> Base 'HReal
      -> ( Base 'HReal , Term 'HReal -> Term 'HReal )
liftB f (Dirac_ e)        = (Dirac_ (invert f @@ e) , const $ Real 1)
liftB f Lebesgue_         = (Lebesgue_              , abs_ . diff (invert f))
liftB f (Mixture leb  es) = (Mixture leb invfes     , if leb then g
                                                      else const $ Real 1)
    where invfes          = [invert f @@ e | e <- es]
          g t             = if_ (or_ [Equal t e | e <- invfes])
                                (Real 1)
                                (snd (liftB f Lebesgue_) t)
liftB f b                 = (LiftB f b              , Jacobian f b)

constrainInv :: (Sing a)
             => Invertible
             -> Base 'HReal
             -> Term 'HReal
             -> Term 'HReal
             -> (Heap -> D (Term ('HMeasure a)))
             -> Heap
             -> D (Term ('HMeasure a))
constrainInv f b e t c h = let (b',g) = liftB f b
                           in emit [observe (t `inRng` f), Factor (g t)] $
                              constrainValue e b' (invert f @@ t) c h

constrainOutcome :: (Sing a, Sing b)
                 => Term ('HMeasure a)
                 -> Base a
                 -> Term a
                 -> (Heap -> D (Term ('HMeasure b)))
                 -> Heap
                 -> D (Term ('HMeasure b))
constrainOutcome e b t c h = track "constrainOutcome" st $ (<<|) e b t c h
    where st = (e,h,Just b,Just t)
                    
(<<|) :: (Sing a, Sing b)
      => Term ('HMeasure a)
      -> Base a
      -> Term a
      -> (Heap -> D (Term ('HMeasure b)))
      -> Heap
      -> D (Term ('HMeasure b))
(<<|) Lebesgue       b t c h = divide Lebesgue_ b t >>= emit # (c h)
(<<|) (Dirac e)      b t c h = constrainValue e b t c h
(<<|) (Normal mu sd) b t c h = divide Lebesgue_ b t >>= emit # 
                               (c (store (Factor $ normalDensity mu sd t) h))
(<<|) (Do g m)       b t c h = constrainOutcome m b t c (store g h)
(<<|) (MPlus m m')   b t c h = liftM2 MPlus (constrainOutcome m  b t c h)
                                            (constrainOutcome m' b t c h)
(<<|) (If ce mt me)  b t c h = let m = mplus_ (when_ ce mt) (unless_ ce me)
                               in constrainOutcome m b t c h
(<<|) Fail           _ _ _ _ = return Fail
(<<|) e              b t c h =
    if (atomic e h)
    then return (Error "constrain outcome: cannot observe measures")
    else if not (hnf e h)
         then evaluate e (\m -> constrainOutcome m b t c) h
         else return (Error "constrain outcome: unknown Measure hnf")

                    
constrainValue :: (Sing a, Sing b)
               => Term a
               -> Base a
               -> Term a
               -> (Heap -> D (Term ('HMeasure b)))
               -> Heap
               -> D (Term ('HMeasure b))
constrainValue e b t c h = track "constrainValue" st $ (<|) e b t c h
    where st = (e,h,Just b,Just t)

(<|) :: (Sing a, Sing b)
     => Term a
     -> Base a
     -> Term a
     -> (Heap -> D (Term ('HMeasure b)))
     -> Heap
     -> D (Term ('HMeasure b))
-- (<|) Unit       b t c h = divide (Dirac_ Unit)     b t >>= emit # (c h)
(<|) Unit (Dirac_ Unit) t c h = c h
(<|) (Real r)   b t c h = divide (Dirac_ (Real r)) b t >>= emit # (c h)
(<|) (Neg e)    b t c h = constrainInv Neg_ b e t c h
(<|) (Recip e)  b t c h = constrainInv Recip_ b e t c h
(<|) (Exp e)    b t c h = constrainInv Exp_ b e t c h
(<|) (Log e)    b t c h = constrainInv Log_ b e t c h
(<|) (Abs e)    b t c h = liftM2 MPlus (constrainInv Abs_Pos b e t c h)
                                       (constrainInv Abs_Neg b e t c h)
(<|) (Sqrt e)   b t c h = liftM2 MPlus (constrainInv Sqrt_Pos b e t c h)
                                       (constrainInv Sqrt_Neg b e t c h)
(<|) (Square e) b t c h = liftM2 MPlus (constrainInv Square_Pos b e t c h)
                                       (constrainInv Square_Neg b e t c h)
(<|) (Add e e') b t c h = lub (evaluate e  (\v  -> constrainInv (Add_ v)  b e' t c) h)
                              (evaluate e' (\v' -> constrainInv (Add_ v') b e  t c) h)
(<|) (Mul e e') b t c h = lub (evaluate e  (\v  -> constrainInv (Mul_ v)  b e' t c) h)
                              (evaluate e' (\v' -> constrainInv (Mul_ v') b e  t c) h)
(<|) (Fst e)    b t c h = flip (evaluate e) h $ \v h' ->
                          case v of
                            Pair e' _ -> constrainValue e' b t c h'
                            _ -> if (atomic v h')
                                 then bot -- divide (Dirac_ (Fst v)) b t >>= emit # (c h')
                                 else return (Error "constrainValue.fst: \
                                                    \unknown HPair hnf")
(<|) (Snd e)    b t c h = flip (evaluate e) h $ \v h' ->
                          case v of
                            Pair _ e' -> constrainValue e' b t c h'
                            _ -> if (atomic v h')
                                 then bot -- divide (Dirac_ (Snd v)) b t >>= emit # (c h')
                                 else return (Error "constrainValue.snd: \
                                                    \unknown HPair hnf")
(<|) (If e tb eb) b          t c h = let m = mplus_ (when_ e (Dirac tb)) (unless_ e (Dirac eb))
                                     in constrainOutcome m b t c h
-- (<|) (Equal e e') b t c = return (Error "TODO constrainValue Equal")
-- (<|) (Less e e') b t c = return (Error "TODO constrainValue Less")
-- (<|) (Or e e') b t c = return (Error "TODO constrainValue Or")
(<|) (Inl e)    (Either b _) t c h = outl t (\v -> constrainValue e b v c) h
(<|) (Inr e)    (Either _ b) t c h = outr t (\v -> constrainValue e b v c) h
(<|) (Pair e e') (Bindx b f) t c h = let c' = constrainValue e' (f (frst t)) (scnd t) c
                                     in constrainValue e b (frst t) c' h                                     
(<|) (Var x) b t c h = case (retrieve x h) of
                         Just (h2,g,h1) ->
                             let c' = c . link h2 (x :<~ Dirac t)
                             in case g of
                                  (_ :<~ m)     -> constrainOutcome (unsafeCoerce m) b t c' h1
                                  (LetInl _ e0) -> evaluate (unsafeLeft e0) (\v0 -> outl v0 (\e -> constrainValue e b t c')) h1
                                  (LetInr _ e0) -> evaluate (unsafeRight e0) (\v0 -> outr v0 (\e -> constrainValue e b t c')) h1
                                  _ -> error "bwdEval let inl / inr undefined"
                         Nothing        -> bot -- divide (Dirac_ (Var x)) b t >>= emit # (c h)
(<|) e       b t c h = if (hnf e h)
                       then bot -- divide (Dirac_ e) b t >>= emit # (c h)
                       else return (Error "constrain value: unknown term")


perform :: (Sing a, Sing b)
        => Term ('HMeasure a)
        -> (Term a -> Heap -> D (Term ('HMeasure b)))
        -> Heap
        -> D (Term ('HMeasure b))
perform e k h = track "perform" st $ (|>>) e k h
    where st = (e,h,Nothing::Maybe(Base a),Nothing::Maybe(Term a))

(|>>) :: (Sing a, Sing b)
      => Term ('HMeasure a)
      -> (Term a -> Heap -> D (Term ('HMeasure b)))
      -> Heap
      -> D (Term ('HMeasure b))
(|>>) Lebesgue       k h = freshVar "l" >>= \z -> emit [z :<~ Lebesgue] (k (Var z) h)
(|>>) (Dirac e)      k h = evaluate e k h
(|>>) (Normal mu sd) k h = flip (evaluate mu) h $ \v -> evaluate sd $ \v' h' ->
                           freshVar "n" >>= \z -> emit [z :<~ Normal v v'] (k (Var z) h')
(|>>) (Do g m)       k h = perform m k (store g h)
(|>>) (MPlus m m')   k h = liftM2 MPlus (perform m k h) (perform m' k h)
(|>>) (If c mt me)   k h = perform (mplus_ (when_ c mt) (unless_ c me)) k h
(|>>) Fail           _ _ = return Fail
(|>>) e              k h =
    if (atomic e h)
    then freshVar "u" >>= \z -> emit [z :<~ e] (k (Var z) h)
    else if not (hnf e h) then evaluate e (\m -> perform m k) h
         else return (Error "perform: unknown Measure hnf")

evaluate :: (Sing a, Sing b)
         => Term a
         -> (Term a -> Heap -> D (Term ('HMeasure b)))
         -> Heap
         -> D (Term ('HMeasure b))
evaluate e k h = track "evaluate" st $ (|>) e k h
    where st = (e,h,Nothing::Maybe(Base a),Nothing::Maybe(Term a))
    
(|>) :: (Sing a, Sing b)
     => Term a
     -> (Term a -> Heap -> D (Term ('HMeasure b)))
     -> Heap
     -> D (Term ('HMeasure b))
(|>) Pi             k h = k Pi h
(|>) r@(Real _)     k h = k r h
(|>) (Neg e)        k h = evaluate e (k . neg) h
(|>) (Abs e)        k h = evaluate e (k . abs_) h
(|>) (Recip e)      k h = evaluate e (k . reciprocal) h
(|>) (Exp e)        k h = evaluate e (k . exponential) h
(|>) (Log e)        k h = evaluate e (k . logarithm) h
(|>) (Sqrt e)       k h = evaluate e (k . sqrroot) h
(|>) (Square e)     k h = evaluate e (k . square) h
(|>) (Add e e')     k h = evaluate e (\v -> evaluate e' $ \v' -> k (add v v')) h
(|>) (Mul e e')     k h = evaluate e (\v -> evaluate e' $ \v' -> k (mul v v')) h
-- (|>) (Not e)        k = evaluate e (k . Not)
-- (|>) (And e e')     k = evaluate e $ \v -> evaluate e' $ \v' -> k (And v v')
(|>) (Equal e e')   k h = evaluate e (\v -> evaluate e' $ \v' -> k (Equal v v')) h
(|>) (Less e e')    k h = evaluate e (\v -> evaluate e' $ \v' -> k (less v v')) h
(|>) (Or e e')      k h = evaluate e (\v -> evaluate e' $ \v' -> k (Or v v')) h
(|>) l@(Inl _)      k h = k l h -- evaluate e (k . Inl) h
(|>) r@(Inr _)      k h = k r h -- evaluate e (k . Inr) h
(|>) Unit           k h = k Unit h
(|>) p@(Pair _ _)   k h = k p h
(|>) (Fst e)        k h = flip (evaluate e) h $ \v h' ->
                          case v of
                            Pair e' _ -> evaluate e' k h'
                            _ -> if (atomic v h')
                                 then k (Fst v) h'
                                 else return (Error "evaluate.fst: unknown HPair hnf")
(|>) (Snd e)        k h = flip (evaluate e) h $ \v h' ->
                          case v of                          
                            Pair _ e' -> evaluate e' k h'
                            _ -> if (atomic v h')
                                 then k (Snd v) h'
                                 else return (Error "evaluate.snd: unknown HPair hnf")
(|>) (If c t e)     k h = evaluate c # h $ \v h' ->
                          case v of
                            Inl Unit -> evaluate t k h'
                            Inr Unit -> evaluate e k h'
                            _        -> evaluate t # h' $ \vt ->
                                        evaluate e (\ve -> k (If v vt ve))
(|>) Lebesgue       k h = k Lebesgue h
(|>) d@(Dirac _)    k h = k d h
(|>) n@(Normal _ _) k h = k n h
(|>) b@(Do _ _)     k h = k b h
(|>) m@(MPlus _ _)  k h = k m h
(|>) Fail           k h = k Fail h
(|>) (Var x)        k h = case (retrieve x h) of
                            Just (h2,g,h1) ->
                                case g of
                                  (_ :<~ m)     -> perform (unsafeCoerce m) (\v -> k v . link h2 (x :<~ Dirac v)) h1
                                  (LetInl _ e0) -> evaluate (unsafeLeft e0) (\v0 -> outl v0 (\e -> evaluate e (\v -> k v . link h2 (x :<~ Dirac v)))) h1
                                  (LetInr _ e0) -> evaluate (unsafeRight e0) (\v0 -> outr v0 (\e -> evaluate e (\v -> k v . link h2 (x :<~ Dirac v)))) h1
                            Nothing -> k (Var x) h
(|>) e              k h = if (hnf e h) then k e h
                          else return (Error "evaluate: unknown term")



-- | Applying base variable substitution
-----------------------------------------

class Reanimate a b where
    reanimateWith :: Sigma -> a -> b

-- | Meant to be used for `Constraint`s
-- TODO(pravnar): why are `Constraint`s universally quantified, rather
-- than being restricted to `Base 'HReal`s?
instance Reanimate (Base 'HReal, Base 'HReal) (Term 'HReal -> D [Guard Var]) where
    reanimateWith sigma (groundbase, unknownbase) = divide groundbase (findBase unknownbase sigma)

-- stuff below this line does not typecheck
-- instance Reanimate (Term a) (D (Term a)) where
--     reanimateWith sigma (Do (Divide groundbase unknownbase t) m)
--         = reanimateWith sigma m >>= \m' ->
--           reanimateWith sigma t >>= \t' ->
--           reanimateWith sigma (groundbase, unknownbase) t' >>= \gs ->
--           return (do_ gs m')
