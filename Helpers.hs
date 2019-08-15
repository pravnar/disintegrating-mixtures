{-# LANGUAGE GADTs, 
             DataKinds,
             RankNTypes,
             TypeSynonymInstances,
             FlexibleInstances,
             TypeOperators #-}

module Helpers where

import Syntax
import Pretty
import Control.Monad.State
import Data.List (find, nub)
import Data.Maybe (catMaybes, fromMaybe, fromJust)
import Data.Set as S (empty, union, Set(..), unions)
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.HashMap.Strict as M
import Prelude hiding (div)
-- import Debug.Trace

-- | For dealing with Hakaru types
----------------------------------------------------------------------

typeOf :: Term a -> Type a
typeOf Pi = sing
typeOf (Real _) = sing
typeOf (Neg _) = sing
typeOf (Abs _) = sing
typeOf (Recip _) = sing
typeOf (Exp _) = sing
typeOf (Log _) = sing
typeOf (Sqrt _) = sing
typeOf (Square _ ) = sing
typeOf (Add _ _) = sing
typeOf (Mul _ _) = sing
typeOf (Inl e) = TEither (typeOf e) sing
typeOf (Inr e) = TEither sing (typeOf e)
typeOf (Equal _ _) = sing
typeOf (Less _ _) = sing
typeOf (Or _ _) = sing
typeOf Unit = sing
typeOf (Pair a b) = TPair (typeOf a) (typeOf b)
typeOf (Fst e) = case typeOf e of (TPair a _) -> a
typeOf (Snd e) = case typeOf e of (TPair _ b) -> b
typeOf (If _ e _) = typeOf e
typeOf Fail = sing
typeOf Lebesgue = sing
typeOf (Dirac e) = TMeasure (typeOf e)
typeOf (Normal _ _) = sing
typeOf (Do _ m) = typeOf m
typeOf (MPlus m _) = typeOf m
typeOf (Var _) = sing
typeOf (Jacobian _ _ _) = sing
typeOf (Error _) = sing

typeOf_ :: Base a -> Type a
typeOf_ (Var_ _ _) = sing
typeOf_ (LiftB _ _) = sing
typeOf_ Lebesgue_ = sing
typeOf_ (Dirac_ e) = typeOf e
typeOf_ (Either b b') = TEither (typeOf_ b) (typeOf_ b')
typeOf_ (Bindx b f) = TPair (typeOf_ b) (typeOf_ $ f (Error "dummy"))
typeOf_ (Mixture _ _) = sing
typeOf_ (Error_ _) = sing

jmEq :: Type a -> Type b -> Maybe (a :~: b)
jmEq TUnit TUnit = Just Refl
jmEq TReal TReal = Just Refl
jmEq (TEither l1 r1) (TEither l2 r2) =
    case jmEq l1 l2 of
      Just Refl -> case jmEq r1 r2 of
                     Just Refl -> Just Refl
                     Nothing   -> Nothing
      Nothing   -> Nothing
jmEq (TPair l1 r1) (TPair l2 r2) =
    case jmEq l1 l2 of
      Just Refl -> case jmEq r1 r2 of
                     Just Refl -> Just Refl
                     Nothing   -> Nothing
      Nothing   -> Nothing
jmEq (TMeasure a) (TMeasure b) =
    case jmEq a b of
      Just Refl -> Just Refl
      Nothing   -> Nothing
jmEq _ _ = Nothing

-- | For checking equality of Hakaru expressions
----------------------------------------------------------------------

{- Just True  ↦ Yes
   Just False ↦ No
   Nothing    ↦ Do not know -}

yes,no,unknown :: Maybe Bool
yes = Just True
no  = Just False
unknown = Nothing

isYes :: Maybe Bool -> Bool
isYes = (== yes) 

ifYesElse :: a -> a -> Maybe Bool -> a
ifYesElse t e mb = if isYes mb then t else e

both :: Maybe Bool -> Maybe Bool -> Maybe Bool
both m1 m2 = liftM2 (&&) m1 m2

realOp :: Term 'HReal -> Term 'HReal -> (Rational -> Rational) -> Maybe Bool
realOp (Real r) (Real r') f = Just $ f r == f r'
realOp e        e'        _ = termEq e e'

realOp2 :: Term 'HReal -> Term 'HReal -> Term 'HReal -> Term 'HReal
        -> (Rational -> Rational -> Rational) -> Maybe Bool
realOp2 (Real a) (Real a') (Real b) (Real b') f = Just $ f a a' == f b b'
realOp2 a a' b b' _ = both (termEq a b) (termEq a' b')

commute :: Maybe Bool -> Maybe Bool -> Maybe Bool
commute m1 m2 = let r = catMaybes [m1,m2]
                in if null r then Nothing else Just (any id r)

termEq :: Term a -> Term b -> Maybe Bool
termEq Unit         Unit              = Just True          
termEq Pi           Pi                = Just True
termEq r@(Real _)   r'@(Real _)       = realOp r r' id
termEq (Neg e)      (Neg e')          = realOp e e' negate
termEq (Abs e)      (Abs e')          = realOp e e' abs
termEq (Recip e)    (Recip e')        = realOp e e' recip
termEq (Exp e)      (Exp e')          = termEq e e'
termEq (Log e)      (Log e')          = termEq e e'
termEq (Sqrt e)     (Sqrt e')         = termEq e e'
termEq (Square e)   (Square (Neg e')) = realOp e e' (^(2::Integer))
termEq (Square e)   (Square e')       = realOp e e' (^(2::Integer))
termEq (Add a a')   (Add b b')        = commute (realOp2 a a' b  b' (+))
                                                (realOp2 a a' b' b  (+))
termEq (Mul a a')   (Mul b b')        = commute (realOp2 a a' b  b' (*))
                                                (realOp2 a a' b' b  (*))
termEq (Inl e)      (Inl e')          = termEq e e'
termEq (Inr e)      (Inr e')          = termEq e e'
termEq (Less a a')  (Less b b')       = realOp2 a a' b b' $ \x y ->
                                        if x <= y then 1 else 0
termEq (Pair a a')  (Pair b b')       = both (termEq a b) (termEq a' b')
termEq (Fst e)      (Fst e')          = termEq e e'
termEq (Snd e)      (Snd e')          = termEq e e'
termEq (If c t e)   (If c' t' e')     = both (termEq c c')
                                             (both (termEq t t') (termEq e e'))
termEq Fail         Fail              = Just True
termEq Lebesgue     Lebesgue          = Just True
termEq (Dirac e)    (Dirac e')        = termEq e e'
termEq (Normal m s) (Normal m' s')    = both (termEq m m') (termEq s s')
termEq (Do g m)     (Do g' m')        = both (guardEq g g') (termEq m m')
termEq (MPlus a a') (MPlus b b')      = commute (both (termEq a b) (termEq a' b'))
                                                (both (termEq a b') (termEq a' b))
termEq (Var v)      (Var v')          = if v == v' then Just True else Nothing
termEq (Error _)    (Error _)         = Nothing
termEq _            _                 = Nothing

guardEq :: Guard Var -> Guard Var -> Maybe Bool
guardEq (_ :<~ m)    (_ :<~ m')    = termEq m m'
guardEq (Factor e)   (Factor e')   = termEq e e'
guardEq (LetInl _ e) (LetInl _ e') = termEq e e'
guardEq (LetInr _ e) (LetInr _ e') = termEq e e'
guardEq (Divide b c t) (Divide b' c' t') =
    case jmEq (typeOf_ b) (typeOf_ b') of
      Just Refl -> case jmEq (typeOf_ c) (typeOf_ c') of
                     Just Refl -> both (termEq t t') $
                                  both (baseEq b b') (baseEq c c')
                     Nothing   -> Just False
      Nothing   -> Just False
guardEq _            _             = Just False
                                     
baseEq :: Base a -> Base a -> Maybe Bool
baseEq Lebesgue_      Lebesgue_        = Just True
baseEq (Dirac_ e)     (Dirac_ e')      = termEq e e'
baseEq (Either l r)   (Either l' r')   = both (baseEq l l') (baseEq r r')
baseEq (Bindx b f)    (Bindx b' f')    = Nothing
baseEq (Mixture l es) (Mixture l' es') = Nothing -- TODO
baseEq (Var_ v _)     (Var_ v' _)      = Just (v == v')
baseEq (LiftB f b)    (LiftB f' b')    = Nothing -- TODO
baseEq (Error_ s)     (Error_ s')      = Nothing

jmTermEq :: Term a -> Term b -> Bool
jmTermEq e e' = case jmEq (typeOf e) (typeOf e') of
                  Just Refl -> isYes (termEq e e')
                  Nothing   -> False

instance Eq InScope where
    IS t == IS t' = jmTermEq t t'

instance Eq (Term a) where
    (==) = jmTermEq
 
-- | For the disintegration monad
----------------------------------------------------------------------

bot :: D a
bot = mzero

lub :: D a -> D a -> D a
lub = mplus

emit :: (Sing a) => [Guard Var] -> D (Term ('HMeasure a)) -> D (Term ('HMeasure a))
emit = liftM . do_

record :: Constraint -> D ()
record c = get >>= \(Env ns cs) -> put $ Env ns (c:cs)

-- | For manipulating heaps
----------------------------------------------------------------------

match :: Var -> Guard Var -> Bool
match x (y :<~ _)    = x == y
match x (LetInl y _) = x == y
match x (LetInr y _) = x == y
match _ _            = False

retrieve :: Var -> Heap -> Maybe (Heap, Guard Var, Heap)
retrieve x h =
  case (break (match x) h) of
    (h2, g:h1) -> Just (h2, g, h1)
    -- (h2, (_ :<~ m):h1)    -> Just (h2, M (unsafeCoerce m), h1)
    -- (h2, (LetInl _ e):h1) -> Just (h2, L (unsafeCoerce e), h1)
    -- (h2, (LetInr _ e):h1) -> Just (h2, R (unsafeCoerce e), h1)
    _                     -> Nothing

unsafeLeft :: Term ('HEither a b) -> Term ('HEither a' b)
unsafeLeft = unsafeCoerce

unsafeRight :: Term ('HEither a b) -> Term ('HEither a b')
unsafeRight = unsafeCoerce

store :: Guard Var -> Heap -> Heap
-- store g@(x :<~ _)    h = guard (not $ any (match x) h) >> return (g:h)
-- store g@(LetInl x _) h = guard (not $ any (match x) h) >> return (g:h)
-- store g@(LetInr x _) h = guard (not $ any (match x) h) >> return (g:h)
-- store g              h = return (g:h)
store g@(x :<~ _) = checkAndPush
    where checkAndPush h =
              if any (match x) h
              then error $ "Variable " ++ name x ++ " is already on heap"
              else g : h
store g = (g:)

link :: Heap -> Guard Var -> Heap -> Heap
link younger binding older = younger ++ [binding] ++ older

-- | For solving base measure constraints
----------------------------------------------------------------------
           
type S = State (Names, [(InScope, InScope)])

first :: (a -> a') -> (a,b) -> (a',b)
first f (a,b) = (f a, b)

second :: (b -> b') -> (a,b) -> (a,b')
second f (a,b) = (a, f b)

instance HasNames S where
    getNames = gets fst
    putNames n = modify (first (const n))
                 
associate :: (Sing a) => Term a -> Term a -> (InScope, InScope)
associate t t' = (IS t, IS t')

populateWith :: [InScope] -> S [InScope]
populateWith []          = return []
populateWith (IS t : es) =
    do assocs <- gets snd
       e' <- if any (mapsTerm t) assocs
             then return (snd . fromJust $ findAssoc t assocs)
             else do v <- Var <$> freshVar "v"
                     modify $ second ((:) (associate t v))
                     return (IS v)
       es' <- populateWith es
       return (e':es')

mapsTerm :: (Sing a) => Term a -> (InScope, InScope) -> Bool
mapsTerm t (e,_) = IS t == e

findAssoc :: (Sing a) => Term a -> [(InScope,InScope)] -> Maybe (InScope,InScope)
findAssoc = find . mapsTerm

findDefault :: (Sing a) => Term a -> S (Term a) -> S (Term a)
findDefault t dflt = do
  assocs <- gets snd
  case findAssoc t assocs of
    Just (_, IS t') -> case jmEq (typeOf t) (typeOf t') of
                         Just Refl -> return t'
                         Nothing   -> error ("Unequal types of associated terms "
                                             ++ show t ++ " and " ++ show t')
    Nothing         -> dflt

type C = forall a. (Sing a) => Term a -> S (Term a) -> S (Term a)

substs :: C -> Term a -> S (Term a)
substs c = go
    where go Pi = return Pi
          go t@(Real _) = return t
          go t@(Neg e) = c t (Neg <$> substs c e)
          go t@(Abs e) = c t (Abs <$> substs c e)
          go t@(Recip e) = c t (Recip <$> substs c e)
          go t@(Exp e) = c t (Exp <$> substs c e)
          go t@(Log e) = c t (Log <$> substs c e)
          go t@(Sqrt e) = c t (Sqrt <$> substs c e)
          go t@(Square e) = c t (Square <$> substs c e)
          go t@(Add e e') = c t (liftM2 Add (substs c e) (substs c e'))
          go t@(Mul e e') = c t (liftM2 Mul (substs c e) (substs c e'))
          go t@(Inl e) = c t (Inl <$> substs c e)
          go t@(Inr e) = c t (Inr <$> substs c e)
          go t@(Equal e e') = c t (liftM2 Equal (substs c e) (substs c e'))
          go t@(Less e e') = c t (liftM2 Less (substs c e) (substs c e'))
          go t@(Or e e') = c t (liftM2 Or (substs c e) (substs c e'))
          go Unit = return Unit
          go t@(Pair e e') = c t (liftM2 Pair (substs c e) (substs c e'))
          go t@(Fst e) = c t (Fst <$> substs c e)
          go t@(Snd e) = c t (Snd <$> substs c e)
          go t@(If e e1 e2) = c t (liftM3 If (substs c e) (substs c e1) (substs c e2))
          go Fail = return Fail
          go Lebesgue = return Lebesgue
          go t@(Dirac e) = c t (Dirac <$> substs c e)
          go t@(Normal e e') = c t (liftM2 Normal (substs c e) (substs c e'))
          go t@(Do g m) = c t (liftM2 Do (gSubsts c g) (substs c m))
          go t@(MPlus m m') = c t (liftM2 MPlus (substs c m) (substs c m'))
          go t@(Var _) = c t (return t)
          go t@(Jacobian f b e) = c t (liftM2 (Jacobian f) (bSubsts c b) (substs c e))
          go t@(Error _) = return t

gSubsts :: C -> Guard Var -> S (Guard Var)
gSubsts c = go
    where go (x :<~ m) = (x :<~) <$> substs c m
          go (Factor e) = Factor <$> substs c e
          go (LetInl x e) = LetInl x <$> substs c e
          go (LetInr x e) = LetInr x <$> substs c e
          go (Divide b b' e) = liftM3 Divide (bSubsts c b) (bSubsts c b') (substs c e)

bSubsts :: C -> Base a -> S (Base a)
bSubsts c = go
    where go b@(Var_ _ _) = return b
          go (LiftB f b) = LiftB f <$> bSubsts c b
          go Lebesgue_ = return Lebesgue_
          go (Dirac_ e) = Dirac_ <$> substs c e
          go (Either b b') = liftM2 Either (bSubsts c b) (bSubsts c b')
          go (Bindx b f) = error "TODO: bSubsts bindx"
          go (Mixture l es) = Mixture l <$> mapM (substs c) es
          go b@(Error_ _) = return b

freeVars :: [Var] -> Term a -> [Var]
freeVars _  Pi = []
freeVars _  (Real _) = []
freeVars vs (Neg e) = freeVars vs e
freeVars vs (Abs e) = freeVars vs e
freeVars vs (Recip e) = freeVars vs e
freeVars vs (Exp e) = freeVars vs e
freeVars vs (Log e) = freeVars vs e
freeVars vs (Sqrt e) = freeVars vs e
freeVars vs (Square e) = freeVars vs e
freeVars vs (Add e e') = freeVars vs e ++ freeVars vs e'
freeVars vs (Mul e e') = freeVars vs e ++ freeVars vs e'
freeVars vs (Inl e) = freeVars vs e
freeVars vs (Inr e) = freeVars vs e
freeVars vs (Equal e e') = freeVars vs e ++ freeVars vs e'
freeVars vs (Less e e') = freeVars vs e ++ freeVars vs e'
freeVars vs (Or e e') = freeVars vs e ++ freeVars vs e'
freeVars _  Unit = []
freeVars vs (Pair e e') = freeVars vs e ++ freeVars vs e'
freeVars vs (Fst e) = freeVars vs e
freeVars vs (Snd e) = freeVars vs e
freeVars vs (If e e1 e2) = freeVars vs e ++ freeVars vs e1 ++ freeVars vs e2
freeVars _  Fail = []
freeVars _  Lebesgue = []
freeVars vs (Dirac e) = freeVars vs e
freeVars vs (Normal e e') = freeVars vs e ++ freeVars vs e'
freeVars vs (Do g m) = gFreeVars vs g ++ freeVars vs m
freeVars vs (MPlus m m') = freeVars vs m ++ freeVars vs m'
freeVars vs (Var v) = if elem v vs then [] else [v]
freeVars vs (Jacobian _ b e) = bFreeVars vs b ++ freeVars vs e
freeVars vs (Error _) = []

gFreeVars :: [Var] -> Guard Var -> [Var]
gFreeVars vs (_ :<~ m) = freeVars vs m
gFreeVars vs (Factor e) = freeVars vs e
gFreeVars vs (LetInl _ e) = freeVars vs e
gFreeVars vs (LetInr _ e) = freeVars vs e
gFreeVars vs (Divide b b' e) = bFreeVars vs b ++ bFreeVars vs b' ++ freeVars vs e

bFreeVars :: [Var] -> Base a -> [Var]
bFreeVars _ (Var_ _ _) = []
bFreeVars vs (LiftB _ b) = bFreeVars vs b
bFreeVars _ Lebesgue_ = []
bFreeVars vs (Dirac_ e) = freeVars vs e
bFreeVars vs (Either b b') = bFreeVars vs b ++ bFreeVars vs b'
bFreeVars vs (Bindx b f) = bFreeVars vs b ++ bFreeVars vs (f $ Error "dummy")
bFreeVars vs (Mixture _ es) = concatMap (freeVars vs) es
bFreeVars vs (Error_ _) = []

getVar :: InScope -> Var
getVar (IS (Var v)) = v
getVar (IS t)       = error ("Something went wrong, got " ++
                             show t ++ "instead of a Var term")

solve :: Constraint -> S Constraint
solve c@(Lebesgue_ :<: Var_ v es) =
    do es' <- populateWith es
       return (Lebesgue_ :<: Var_ v es')
solve c@(Dirac_ e :<: b@(Var_ v es)) =
    do es' <- populateWith es
       e' <- substs findDefault e
       allowedVars <- gets (map (getVar . snd) . snd)
       let fvs = freeVars allowedVars e'
           num = if null fvs then Dirac_ e'
                 else Error_ ("unbound variable(s) " ++ show fvs ++
                              " in " ++ show (Dirac_ e'))
       return (num :<: Var_ v es')
solve c@(b :<: b'@(Var_ _ _))
    = return $ Error_ ("don't know how to solve for numerator " ++ show b) :<: b'
solve c@(_ :<: b) = error ("Denominator has non-variable base" ++ show b)

numer :: Constraint -> Base 'HReal
numer (Lebesgue_ :<: _)       = Lebesgue_
numer (b@(Dirac_ e) :<: _)    =
    case jmEq (typeOf e) TReal of
      Just Refl -> Dirac_ e
      Nothing   -> Error_ ("numerator has non-real base " ++ show b)
numer (b@(Mixture _ _) :<: _) = b
numer (Error_ s :<: _)        = Error_ s
numer (b :<: _)               = Error_ $ "numerator has base " ++ show b

denom :: Constraint -> Base 'HReal
denom (_ :<: b@(Var_ _ _)) = b
denom (_ :<: b) = error ("non-variable denominator " ++ show b)

bVar :: Base 'HReal -> BVar
bVar (Var_ v _) = v
bVar b = error ("bVar: non-variable base " ++ show b)

inScope :: Base 'HReal -> [InScope]
inScope (Var_ _ es) = es
inScope b = error ("inScope: non-variable base " ++ show b)

findVarOnly :: (Sing a) => Term a -> S (Term a) -> S (Term a)
findVarOnly t@(Var _) s = findDefault t s
findVarOnly _ s = s

type BaseClosure = ([InScope], Base 'HReal)
type Sigma = M.HashMap BVar BaseClosure    

-- | Assumption: all denominators are "variable" bases
--   Assumption: if two constraints have the same denominator, then
--   they have the same binding lists of terms "in scope"
group :: [Constraint] -> M.HashMap BVar BaseClosure
group = foldr groupByDenom M.empty
    where groupByDenom c = M.insertWith (f c)
                                        (bVar $ denom c)
                                        (inScope (denom c) , numer c)
          f c (es1, b1) (es2, b2)
              | length es1 == length es2 =
                  let varsInScope (IS t) = varsIn t
                      init = ( Names 0 (S.unions . map varsInScope $ es1++es2) , [] )
                      newvars :: [Term 'HReal]
                      newvars = flip evalState init $
                                replicateM (length es1) (Var <$> (freshVar "v" :: S Var))
                      newIS = map IS newvars
                      b1' = modifyBase (es1,b1) newIS
                      b2' = modifyBase (es2,b2) newIS
                  in (newIS, bplus b1' b2')
                  -- (es1, bplus b1 b2)
              | otherwise  = error ("group: mismatched inScope lengths in " ++ show es1
                                   ++ " and " ++ show es2 ++ " with c = " ++ show c)

modifyBase :: BaseClosure -> [InScope] -> Base 'HReal
modifyBase (old,b) new = evalState (bSubsts findVarOnly b) initState
    where assocs = if length old == length new then zip old new
                   else error ("Scope lists of different length:" ++
                               show old ++ " and " ++ show new)
          initState = (Names 0 S.empty, assocs)

fail_ :: Base 'HReal
fail_ = Mixture False []

findBase :: (Sing a) => Base a -> Sigma -> Base a
findBase (Var_ v es)    m = modifyBase (M.lookupDefault (es, fail_) v m) es
findBase (Either b b')  m = Either (findBase b m) (findBase b' m)
findBase (Bindx b f)    m = Bindx (findBase b m) (\x -> findBase (f x) m)
findBase (Dirac_ Unit)  _ = Dirac_ Unit
findBase b              _ = Error_ $ "cannot infer base " ++ show b

-- | Translate base measures into Hakaru measure terms
fromBase :: (Sing a) => Base a -> Term ('HMeasure a)
fromBase Lebesgue_     = Lebesgue
fromBase (Dirac_ a)    = Dirac a
fromBase (Either b b') = MPlus (Do (l :<~ fromBase b)
                                   (Dirac (Inl (Var l))))
                               (Do (r :<~ fromBase b')
                                   (Dirac (Inr (Var r))))
    where (l,r) = (V "l", V "r")
fromBase (Bindx b f)   = do_ [x :<~ fromBase b,
                              y :<~ fromBase (f (Var x))]
                         (Dirac (Pair (Var x) (Var y)))
    where (x,y) = (V "x", V "y")
fromBase (Mixture b es) = msum_ $ (if b then Lebesgue else Fail) : map Dirac es

-- | For combining guards, measure terms, and bases
----------------------------------------------------------------------

gplus :: [Guard Var] -> [Guard Var] -> [Guard Var]
gplus gs gs' = [bindUnit $ mplus_ (diracUnit gs) (diracUnit gs')]

gsum :: [[Guard Var]] -> [Guard Var]
gsum []  = [observe false_]
gsum gss = foldl1 gplus gss

mplus_ :: (Sing a) => Term ('HMeasure a) -> Term ('HMeasure a) -> Term ('HMeasure a)
mplus_ m Fail = m
mplus_ Fail m = m
mplus_ m m'   = MPlus m m'

msum_ :: (Sing a) => [Term ('HMeasure a)] -> Term ('HMeasure a)
msum_ = foldl mplus_ Fail

bplus :: Base 'HReal -> Base 'HReal -> Base 'HReal
bplus Lebesgue_      Lebesgue_       = Mixture True []
bplus Lebesgue_      (Dirac_ t)      = Mixture True [t]
bplus (Dirac_ t)     Lebesgue_       = Mixture True [t]
bplus (Dirac_ s)     (Dirac_ t)      = Mixture False (nub [s,t])
bplus Lebesgue_      (Mixture _ ts)  = Mixture True ts
bplus (Mixture _ ts) Lebesgue_       = Mixture True ts
bplus (Dirac_ t)     (Mixture b ts)  = Mixture b (nub $ t:ts)
bplus (Mixture b ts) (Dirac_ t)      = Mixture b (nub $ t:ts)
bplus (Mixture b ss) (Mixture b' ts) = Mixture (b || b') (nub $ ss++ts)
bplus _            b@(Error_ _)      = b
bplus b@(Error_ _) _                 = b
bplus b b' = Error_ $ "Trying to add " ++ show b ++ " and " ++ show b'

-- | Smart constructors
----------------------------------------------------------------------
             
neg :: Term 'HReal -> Term 'HReal
neg (Real r) = Real (-r)
neg (Neg  e) = e
neg  e       = Neg e

abs_ :: Term 'HReal -> Term 'HReal
abs_ (Real r) = Real (abs r)
abs_ (Neg e)  = e
abs_ e        = Abs e

reciprocal :: Term 'HReal -> Term 'HReal
reciprocal (Real  r) = Real (1/r)
reciprocal (Recip e) = e
reciprocal e         = Recip e

exponential :: Term 'HReal -> Term 'HReal
exponential (Real 0) = Real 1
exponential (Log e)  = e
exponential e        = Exp e

logarithm :: Term 'HReal -> Term 'HReal
logarithm (Real 1) = Real 0
logarithm (Exp e)  = e
logarithm e        = Log e

sqrroot :: Term 'HReal -> Term 'HReal
sqrroot (Real 0)   = Real 0
sqrroot (Real 1)   = Real 1
sqrroot (Square e) = e
sqrroot e          = Sqrt e

square :: Term 'HReal -> Term 'HReal
square (Real r) = Real (r^(2::Integer))
square (Sqrt e) = e
square e        = Square e

add :: Term 'HReal -> Term 'HReal -> Term 'HReal
add (Real r1) (Real r2) = Real (r1+r2)
add (Real  0)  e        = e
add  e        (Real  0) = e
add  e1        e2       = Add e1 e2

mul :: Term 'HReal -> Term 'HReal -> Term 'HReal
mul (Real r1) (Real r2) = Real (r1*r2)
mul (Real  0)  _        = Real 0
mul _         (Real  0) = Real 0
mul (Real  1)  e        = e
mul  e        (Real  1) = e
mul  e1        e2       = Mul e1 e2

div :: Term 'HReal -> Term 'HReal -> Term 'HReal
div e e' = mul e (reciprocal e')

frst :: (Sing a, Sing b) => Term ('HPair a b) -> Term a
frst (Pair a _) = a
frst e          = Fst e

scnd :: (Sing a, Sing b) => Term ('HPair a b) -> Term b
scnd (Pair _ b) = b
scnd  e         = Snd e

minus :: Term 'HReal -> Term 'HReal -> Term 'HReal
minus x y = add x (neg y)

double :: Term 'HReal -> Term 'HReal
double t = mul (Real 2) t

frac :: Term 'HReal -> Term 'HReal -> Term 'HReal
frac num den = mul num (reciprocal den)
                  
normalDensity :: Term 'HReal -> Term 'HReal -> Term 'HReal -> Term 'HReal
normalDensity m s x =
    frac (Exp . Neg $ frac (square $ minus x m) (double (square s)))
         (Mul (Sqrt (double Pi)) s)

stdNormal :: Term ('HMeasure 'HReal)
stdNormal = Normal (Real 0) (Real 1)         

true_ :: TermHBool
true_ = Inl Unit

false_ :: TermHBool
false_ = Inr Unit

observe :: TermHBool -> Guard Var
observe = LetInl (V "_")

observeNot :: TermHBool -> Guard Var
observeNot = LetInr (V "_")

less :: Term 'HReal -> Term 'HReal -> TermHBool
less (Real r) (Real r') = if r < r' then true_ else false_
less e e' = Less e e'

leq :: Term 'HReal -> Term 'HReal -> TermHBool
leq e e' = Or (Less e e') (Equal e e')

or_ :: [TermHBool] -> TermHBool
or_ [] = false_
or_ bs = foldl1 Or bs

if_ :: (Sing a) => TermHBool -> Term a -> Term a -> Term a
if_ (Inl Unit) t _ = t
if_ (Inr Unit) _ e = e
if_ c          t e = If c t e

min_ :: Term 'HReal -> Term 'HReal -> Term 'HReal
min_ t1 t2 = if_ (Less t1 t2) t1 t2

max_ :: Term 'HReal -> Term 'HReal -> Term 'HReal
max_ t1 t2 = if_ (Less t1 t2) t2 t1

when_ :: (Sing a) => TermHBool -> Term ('HMeasure a) -> Term ('HMeasure a)
when_ (Inl Unit) m = m
when_ (Inr Unit) _ = Fail
when_ b          m = Do (observe b) m

unless_ :: (Sing a) => TermHBool -> Term ('HMeasure a) -> Term ('HMeasure a)
unless_ (Inl Unit) _ = Fail
unless_ (Inr Unit) m = m
unless_ b          m = Do (observeNot b) m

weight :: (Sing a) => Term 'HReal -> Term ('HMeasure a) -> Term ('HMeasure a)
weight (Real 0) m = Fail
weight (Real 1) m = m
weight r        m = Do (Factor r) m
                                                          
outl :: (Sing a, Sing b, Sing c)
     => Term ('HEither a b)
     -> (Term a -> Heap -> D (Term ('HMeasure c)))
     -> Heap
     -> D (Term ('HMeasure c))
outl (Inl e) k h = k e h
outl (Inr _) _ _ = return Fail
outl e       k h = freshVar "_l" >>= \x -> Do (LetInl x e) <$> k (Var x) h

outr :: (Sing a, Sing b, Sing c)
     => Term ('HEither a b)
     -> (Term b -> Heap -> D (Term ('HMeasure c)))
     -> Heap
     -> D (Term ('HMeasure c))
outr (Inr e) k h = k e h
outr (Inl _) _ _ = return Fail
outr e       k h = freshVar "_r" >>= \x -> Do (LetInr x e) <$> k (Var x) h


-- | Operations on Invertibles
--------------------------------------------------------------------------

invert :: Invertible -> Invertible
invert Id_         = Id_
invert Neg_        = Neg_
invert Abs_Pos     = Id_
invert Abs_Neg     = Neg_
invert Recip_      = Recip_
invert (Add_ e)    = Sub_ e
invert (Sub_ e)    = Add_ e
invert (Mul_ e)    = Div_ e
invert (Div_ e)    = Mul_ e
invert Exp_        = Log_
invert Log_        = Exp_
invert Square_Pos  = Sqrt_Pos
invert Square_Neg  = Sqrt_Neg
invert Sqrt_Pos    = Square_Pos
invert Sqrt_Neg    = Square_Neg

-- inDom :: Term 'HReal -> Invertible -> Term ('HMeasure 'HBool)
-- inDom _ Id_         = Dirac T
-- inDom _ Neg_        = Dirac T
-- inDom _ Recip_      = Dirac T
-- inDom _ (Add_ _)    = Dirac T
-- inDom _ (Sub_ _)    = Dirac T
-- inDom _ (Mul_ _)    = Dirac T
-- inDom _ (Div_ _)    = Dirac T
-- inDom _ Exp_        = Dirac T                      
-- inDom t Log_        = Dirac $ greater t (Real 0)
-- inDom t (RSquare n) = if_ (Equal n $ Int 1)
--                           (Dirac . geq t $ Real 0)
--                           (Dirac . Less t $ Real 0)
-- inDom t (Sqrt_ _)   = Dirac $ geq t (Real 0)

inRng :: Term 'HReal -> Invertible -> TermHBool
inRng _ Id_         = true_ 
inRng _ Neg_        = true_
inRng t Abs_Pos     = leq (Real 0) t
inRng t Abs_Neg     = leq (Real 0) t
inRng _ Recip_      = true_
inRng _ (Add_ _)    = true_ 
inRng _ (Sub_ _)    = true_ 
inRng _ (Mul_ _)    = true_
inRng _ (Div_ _)    = true_
inRng t Exp_        = leq (Real 0) t
inRng _ Log_        = true_
inRng t Square_Pos  = leq (Real 0) t
inRng t Square_Neg  = leq (Real 0) t
inRng t Sqrt_Pos    = leq (Real 0) t
inRng t Sqrt_Neg    = Less t (Real 0)

apply :: Invertible -> Term 'HReal -> Term 'HReal
apply Id_         t = t
apply Neg_        t = Neg t
apply Abs_Pos     t = Abs t
apply Abs_Neg     t = Abs t
apply Recip_      t = Recip t
apply (Add_ s)    t = Add t s
apply (Sub_ s)    t = minus t s
apply (Mul_ s)    t = Mul t s
apply (Div_ s)    t = frac t s
apply Exp_        t = Exp t
apply Log_        t = Log t
apply Square_Pos  t = Square t
apply Square_Neg  t = Square t
apply Sqrt_Pos    t = Sqrt t
apply Sqrt_Neg    t = Neg (Sqrt t)

(@@) :: Invertible -> Term 'HReal -> Term 'HReal
(@@) = apply

diff :: Invertible -> Term 'HReal -> Term 'HReal
diff Id_         _ = Real 1
diff Neg_        _ = Real (-1)
diff Abs_Pos     _ = Real 1
diff Abs_Neg     _ = Real (-1)
diff Recip_      t = Neg . Recip $ Square t
diff (Add_ _)    _ = Real 1
diff (Sub_ _)    _ = Real 1
diff (Mul_ s)    _ = s
diff (Div_ s)    _ = Recip s
diff Exp_        t = Exp t
diff Log_        t = Recip t
diff Square_Pos  t = Mul (Real 2) t
diff Square_Neg  t = Mul (Real 2) t
diff Sqrt_Pos    t = Mul (Real 0.5) (Recip $ Sqrt t)
diff Sqrt_Neg    t = Neg $ Mul (Real 0.5) (Recip $ Sqrt t)

-- | Other helpers
----------------------------------------------------------------------

atomic :: Term e -> Heap -> Bool
atomic (Real _)       _ = False
atomic (Neg u)        h = atomic u h
atomic (Abs u)        h = atomic u h
atomic (Recip u)      h = atomic u h
atomic (Add u1 u2)    h = (atomic u1 h) || (atomic u2 h)
atomic (Mul u1 u2)    h = (atomic u1 h) || (atomic u2 h)
atomic (Exp u)        h = atomic u h
atomic (Log u)        h = atomic u h 
atomic (Sqrt u)       h = atomic u h
atomic (Square u)     h = atomic u h
atomic (Equal u1 u2)  h = (atomic u1 h) || (atomic u2 h)
atomic (Less u1 u2)   h = (atomic u1 h) || (atomic u2 h)
-- atomic (Not u)     h    = atomic u
-- atomic (And u1 u2) h    = liftM2 (||) (atomic u1) (atomic u2)
atomic (Or u1 u2)     h = (atomic u1 h) || (atomic u2 h)
atomic (Fst u)        h = atomic u h
atomic (Snd u)        h = atomic u h
atomic (If c t e)     h = (atomic c h) || (atomic t h) || (atomic e h)
atomic (Var x)        h = not (any (match x) h)
atomic _              _ = False

hnf :: Term e -> Heap -> Bool
hnf Pi           = const True 
hnf (Real _)     = const True
hnf (Inl _)      = const True
hnf (Inr _)      = const True
hnf Unit         = const True
hnf (Pair  _ _)  = const True
hnf Fail         = const True
hnf Lebesgue     = const True
hnf (Dirac _)    = const True
hnf (Normal _ _) = const True
hnf (Do _ _)     = const True
hnf (MPlus _ _)  = const True
hnf (Error _)    = const True
hnf u            = atomic u

(#) :: (a -> b -> c) -> b -> a -> c
f # b = flip f b

do_ :: (Sing a) => [Guard Var] -> Term ('HMeasure a) -> Term ('HMeasure a)
do_ gs m = foldr Do m gs

wrapHeap :: (Sing a) => Heap -> Term ('HMeasure a) -> Term ('HMeasure a)
wrapHeap h = do_ (reverse h)

diracUnit :: [Guard Var] -> Term ('HMeasure 'HUnit)
diracUnit gs = do_ gs (Dirac Unit)

bindUnit :: Term ('HMeasure 'HUnit) -> Guard Var
bindUnit m = V "_" :<~ m


-- | "Core Hakaru Monad"
----------------------------------------------------------------------
-- State monad with Names, for defining and using measure combinators
-- that bind variables, like bindx or liftMeasure

type CH = State Names

instance HasNames CH where
    getNames = get
    putNames = put

addNewVars :: S.Set String -> Names -> Names
addNewVars new (Names i existing) = Names i (S.union new existing)

addVarsIn :: Term a -> CH ()
addVarsIn = modify . addNewVars . varsIn

liftMeasure :: (Sing a, Sing b)
            => (Term a -> Term b)
            -> Term ('HMeasure a)
            -> CH (Term ('HMeasure b))
liftMeasure f m = do addVarsIn m
                     x <- freshVar "lm"
                     return (Do (x :<~ m) (Dirac (f (Var x))))

pairWithUnit :: (Sing a)
             => Term ('HMeasure a)
             -> CH (Term ('HMeasure ('HPair a 'HUnit)))
pairWithUnit = liftMeasure (\x -> Pair x Unit)

-- Warning: does not do any kind of variable substitution!
-- Assumes that k does not use "B-263-54" as a free variable                                          
bindWithFun :: (Sing a, Sing b, Sing c)
            => (Term a -> Term b -> Term c)
            -> Term ('HMeasure a)
            -> (Term a -> CH (Term ('HMeasure b)))
            -> CH (Term ('HMeasure c))
bindWithFun c m k = do d <- freshVar "dummy"
                       addVarsIn m
                       kd <- k (Var d)
                       addVarsIn kd
                       x <- freshVar "B-263-54-"
                       y <- freshVar "y"
                       kx <- k (Var x)
                       return $ do_ [ x :<~ m
                                    , y :<~ kx ]
                                    (Dirac (c (Var x) (Var y)))

bind :: (Sing a, Sing b)
      => Term ('HMeasure a)
      -> (Term a -> CH (Term ('HMeasure b)))
      -> CH (Term ('HMeasure b))
bind = bindWithFun (\_ b -> b)

bindx :: (Sing a, Sing b)
      => Term ('HMeasure a)
      -> (Term a -> CH (Term ('HMeasure b)))
      -> CH (Term ('HMeasure ('HPair a b)))
bindx = bindWithFun (\a b -> Pair a b)        

productM :: (Sing a, Sing b)
         => Term ('HMeasure a)
         -> Term ('HMeasure b)
         -> CH (Term ('HMeasure ('HPair a b)))
productM m = bindx m . (const.return)

letinl :: (Sing a, Sing b, Sing c)
       => Term ('HEither a b)
       -> (Term a -> CH (Term ('HMeasure c)))
       -> CH (Term ('HMeasure c))
letinl e k = do d <- freshVar "dummy"
                addVarsIn e
                kd <- k (Var d)
                addVarsIn kd
                x <- freshVar "nl"
                kx <- k (Var x)
                return $ Do (LetInl x e) kx

letinr :: (Sing a, Sing b, Sing c)
       => Term ('HEither a b)
       -> (Term b -> CH (Term ('HMeasure c)))
       -> CH (Term ('HMeasure c))
letinr e k = do d <- freshVar "dummy"
                addVarsIn e
                kd <- k (Var d)
                addVarsIn kd
                x <- freshVar "nr"
                kx <- k (Var x)
                return $ Do (LetInr x e) kx

factor :: (Sing a)
       => Term 'HReal
       -> CH (Term ('HMeasure a))
       -> CH (Term ('HMeasure a))
factor e m = m >>= \m' -> return (Do (Factor e) m')

dirac :: (Sing a) => Term a -> CH (Term ('HMeasure a))
dirac = return . Dirac

uniform :: Term 'HReal -> Term 'HReal -> CH (Term ('HMeasure 'HReal))
uniform l r = bind Lebesgue $ \x ->
              letinl (Less l x) $ \_ ->
              letinl (Less x r) $ \_ ->
              factor (reciprocal (minus r l)) $
              dirac x
                    
stdUniform :: CH (Term ('HMeasure 'HReal))
stdUniform = uniform (Real 0) (Real 1)

emptyNames :: Names
emptyNames = Names 0 empty           

evalNames :: CH a -> a
evalNames n = evalState n emptyNames

withDiffNames :: CH a -> CH b -> (a,b)
withDiffNames na nb = evalNames (liftM2 (,) na nb)
