{-# LANGUAGE GADTs, 
             DataKinds, 
             KindSignatures,
             TypeOperators,
             TypeSynonymInstances,
             FlexibleContexts,
             FlexibleInstances,
             ExistentialQuantification,
             StandaloneDeriving #-}

module Syntax where    
import Control.Monad.State
import Data.Set as S (Set, member, insert, empty, union, unions, singleton)
import Data.Hashable (Hashable(..))
import Control.Applicative (Alternative(..))
import Text.PrettyPrint (Doc)

-- | Hakaru types
----------------------------------------------------------------------

data H = HUnit
       | HReal
       | HEither H H
       | HPair H H
       | HMeasure H

type HBool = 'HEither 'HUnit 'HUnit
type TermHBool = Term ('HEither 'HUnit 'HUnit)

data Type (a :: H) where
    TUnit    :: Type 'HUnit
    TReal    :: Type 'HReal
    TEither  :: Type a -> Type b -> Type ('HEither a b)
    TPair    :: Type a -> Type b -> Type ('HPair a b)
    TMeasure :: Type a -> Type ('HMeasure a)

deriving instance Show (Type a)

class Sing (a :: H) where
    sing :: Type a

instance Sing 'HUnit where
    sing = TUnit

instance Sing 'HReal where
    sing = TReal

instance (Sing a, Sing b) => Sing ('HEither a b) where
    sing = TEither sing sing

instance (Sing a, Sing b) => Sing ('HPair a b) where
    sing = TPair sing sing

instance (Sing a) => Sing ('HMeasure a) where
    sing = TMeasure sing

data (a :: H) :~: (b :: H) where
    Refl :: a :~: a
               
-- | Hakaru terms
----------------------------------------------------------------------

data Guard v where
    (:<~)   :: v -> Term ('HMeasure a) -> Guard v
    Factor  :: Term 'HReal -> Guard v
    LetInl  :: (Sing b) => v -> Term ('HEither a b) -> Guard v
    LetInr  :: (Sing a) => v -> Term ('HEither a b) -> Guard v
    Divide  :: Base a -> Base a -> Term a -> Guard v

-- TODO (maybe): add a type parameter
newtype Var = V {name :: String} deriving (Eq)

type Heap = [Guard Var]               

data Term a where
    Pi       :: Term 'HReal
    Real     :: Rational -> Term 'HReal    
    Neg      :: Term 'HReal -> Term 'HReal
    Abs      :: Term 'HReal -> Term 'HReal
    Recip    :: Term 'HReal -> Term 'HReal
    Exp      :: Term 'HReal -> Term 'HReal
    Log      :: Term 'HReal -> Term 'HReal
    Sqrt     :: Term 'HReal -> Term 'HReal
    Square   :: Term 'HReal -> Term 'HReal
    Add      :: Term 'HReal -> Term 'HReal -> Term 'HReal
    Mul      :: Term 'HReal -> Term 'HReal -> Term 'HReal

    Inl      :: (Sing a, Sing b) => Term a -> Term ('HEither a b)
    Inr      :: (Sing a, Sing b) => Term b -> Term ('HEither a b)

    Equal    :: (Sing a) => Term a -> Term a -> TermHBool
    Less     :: Term 'HReal -> Term 'HReal -> TermHBool
    -- Not      :: Term ('HEither 'HUnit 'HUnit) -> Term ('HEither 'HUnit 'HUnit)
    -- And      :: Term 'HBool -> Term 'HBool -> Term 'HBool
    Or       :: TermHBool -> TermHBool -> TermHBool
                
    Unit     ::                     Term 'HUnit
    Pair     :: (Sing a, Sing b) => Term a -> Term b -> Term ('HPair a b)
    Fst      :: (Sing a, Sing b) => Term ('HPair a b) -> Term a
    Snd      :: (Sing a, Sing b) => Term ('HPair a b) -> Term b

    If       :: (Sing a) => TermHBool -> Term a -> Term a -> Term a
                
    Fail        :: (Sing a) => Term ('HMeasure a)
    Lebesgue    :: Term ('HMeasure 'HReal)
    Dirac       :: (Sing e) => Term e -> Term ('HMeasure e)
    Normal      :: Term 'HReal -> Term 'HReal   -> Term ('HMeasure 'HReal)
    -- Uniform     :: Term 'HReal -> Term 'HReal   -> Term ('HMeasure 'HReal)
    -- Beta        :: Term 'HReal -> Term 'HReal   -> Term ('HMeasure 'HReal)
    -- Bern        :: Term 'HReal                 -> Term ('HMeasure 'HBool)
    Do    :: (Sing a) => Guard Var -> Term ('HMeasure a) -> Term ('HMeasure a)
    MPlus :: (Sing a) => Term ('HMeasure a) -> Term ('HMeasure a) -> Term ('HMeasure a)

    Var      :: (Sing e) => Var -> Term e

    Jacobian :: Invertible -> Base 'HReal -> Term 'HReal -> Term 'HReal
    Error    :: (Sing e) => String         -> Term e

    Total    :: (Sing a) => Term ('HMeasure a) -> Term 'HReal
    -- ^ TODO: handle this everywhere!

-- | Base measures                
----------------------------------------------------------------------

data InScope = forall a. (Sing a) => IS (Term a)

-- TODO (maybe): add a type parameter
newtype BVar = B {name_ :: String} deriving (Eq)

instance Hashable BVar where
    hashWithSalt n (B s) = hashWithSalt n s
                
data Base a where
    Var_      :: BVar -> [InScope] -> Base 'HReal
    LiftB     :: Invertible -> Base 'HReal -> Base 'HReal
    Lebesgue_ :: Base 'HReal
    Dirac_    :: Term a -> Base a
    Either    :: (Sing a, Sing b) => Base a -> Base b -> Base ('HEither a b)
    Bindx     :: (Sing a, Sing b) => Base a -> (Term a -> Base b) -> Base ('HPair a b)
    Mixture   :: Bool   -> [Term 'HReal] -> Base 'HReal
    Error_    :: (Sing a) => String -> Base a

class Inferrable a where
    base :: Int -> ([InScope] -> Base a, Int)

instance Inferrable 'HUnit where
    base n = (const (Dirac_ Unit), n)

instance Inferrable 'HReal where
    base n = (Var_ (B $ "b" ++ show n), n+1)

instance (Sing a, Sing b, Inferrable a, Inferrable b) => Inferrable ('HEither a b) where
    base n = let (l,n')  = base n
                 (r,n'') = base n'
             in (\es -> Either (l es) (r es), n'')

instance (Sing a, Sing b, Inferrable a, Inferrable b) => Inferrable ('HPair a b) where
    base n = let (l,n')  = base n
                 (r,n'') = base n'
             in (\es -> Bindx (l es) (\x -> r (IS x : es)), n'')


-- | Invertible functions on the reals, and operations on those functions
--------------------------------------------------------------------------

data Invertible where
    Id_        :: Invertible
    Neg_       :: Invertible
    Abs_Pos    :: Invertible
    Abs_Neg    :: Invertible
    Recip_     :: Invertible
    Add_       :: Term 'HReal -> Invertible
    Sub_       :: Term 'HReal -> Invertible
    Mul_       :: Term 'HReal -> Invertible
    Div_       :: Term 'HReal -> Invertible
    Exp_       :: Invertible
    Log_       :: Invertible
    Square_Pos :: Invertible
    Square_Neg :: Invertible
    Sqrt_Pos   :: Invertible
    Sqrt_Neg   :: Invertible                
                
-- | Things for the disintegration monad    
----------------------------------------------------------------------
    
data Names = Names { _v :: Int
                   , usedVars :: Set String
                   } deriving (Show)

data Constraint = forall a. (Sing a) => (Base a) :<: (Base a)

data Env = Env { names :: Names
               , constraints :: [Constraint] }

data Trace a = Bot
             | Return a
             | Step Doc (Trace a)
             | Lub (Trace a) (Trace a)

instance Monad Trace where
    return           = Return
    Bot        >>= _ = Bot
    Return a   >>= f = f a
    Step doc t >>= f = Step doc (t >>= f)
    Lub t1 t2  >>= f = Lub (t1 >>= f) (t2 >>= f)

instance Functor Trace where
    fmap _ Bot         = Bot
    fmap f (Return a)  = Return (f a)
    fmap f (Step d t)  = Step d (fmap f t)
    fmap f (Lub t1 t2) = Lub (fmap f t1) (fmap f t2)
                       
instance Applicative Trace where
    pure   = return
    (<*>)  = ap

instance MonadPlus Trace where
    mzero = Bot
    mplus = Lub

instance Alternative Trace where
    empty = mzero
    (<|>) = mplus         

type D = StateT Env Trace -- ^ The disintegration monad

runDisintegrate :: D a -> Env -> Trace (a, Env)
runDisintegrate = runStateT

class (Monad m) => HasNames m where
    getNames :: m Names
    putNames :: Names -> m ()

instance HasNames D where
    getNames = gets names
    putNames n = modify (\env -> env {names = n})

{- | Needs to guarantee:
   1. never used for generating the same name twice
   2. does not generate a name that is already used in the program -}
freshVar :: (HasNames m) => String -> m Var
freshVar prefix = do
  n <- getNames
  let (newname, n') = freshName prefix n
  putNames n'
  return (V newname)

freshName :: String -> Names -> (String, Names)
freshName prefix n@(Names counter used) =
    let newname = prefix ++ show counter
    in if member newname used
       then freshName prefix (n {_v = counter+1})
       else (newname, n {usedVars = insert newname used} )

varsIn :: Term e -> Set String
varsIn Pi                   = S.empty
varsIn (Real _)             = S.empty
varsIn (Neg e)              = varsIn e
varsIn (Abs e)              = varsIn e
varsIn (Recip e)            = varsIn e
varsIn (Add e1 e2)          = varsIn e1 `union` varsIn e2
varsIn (Mul e1 e2)          = varsIn e1 `union` varsIn e2
varsIn (Exp e)              = varsIn e
varsIn (Log e)              = varsIn e
varsIn (Sqrt e)             = varsIn e
varsIn (Square e)           = varsIn e
varsIn (Inl e)              = varsIn e
varsIn (Inr e)              = varsIn e 
varsIn (Equal  e e')        = varsIn e `union` varsIn e'
varsIn (Less   e e')        = varsIn e `union` varsIn e'
-- varsIn (Not e)            = varsIn e
-- varsIn (And e1 e2)        = varsIn e1 `union` varsIn e2
varsIn (Or     e e')        = varsIn e `union` varsIn e'
varsIn Unit                 = S.empty
varsIn (Pair e1 e2)         = varsIn e1 `union` varsIn e2
varsIn (Fst e)              = varsIn e
varsIn (Snd e)              = varsIn e
varsIn (If c t e)           = varsIn c `union` varsIn t `union` varsIn e
varsIn Fail                 = S.empty
varsIn Lebesgue             = S.empty
varsIn (Dirac e)            = varsIn e
varsIn (Normal e1 e2)       = varsIn e1 `union` varsIn e2
varsIn (Do (x :<~ m)   e)   = insert (name x) (varsIn m) `union` varsIn e
varsIn (Do (Factor f)  e)   = varsIn f `union` varsIn e
varsIn (Do (LetInl x e) e') = insert (name x) (varsIn e) `union` varsIn e'
varsIn (Do (LetInr x e) e') = insert (name x) (varsIn e) `union` varsIn e'
varsIn (Do (Divide b b' e) e')
    = varsInBase b `union` varsInBase b' `union` varsIn e `union` varsIn e'
varsIn (MPlus m n)          = varsIn m `union` varsIn n
varsIn (Var x)              = singleton (name x)
varsIn (Jacobian _ b e)     = varsInBase b `union` varsIn e
varsIn (Error _)            = S.empty
varsIn (Total e)            = varsIn e

varsInBase :: Base a -> Set String
varsInBase (Var_ _ es)    = unions [varsIn t | IS t <- es]
varsInBase (LiftB _ b)    = varsInBase b
varsInBase (Dirac_ e)     = varsIn e
varsInBase Lebesgue_      = S.empty
varsInBase (Either b b')  = varsInBase b `union` varsInBase b'
varsInBase (Bindx b f)    = varsInBase b `union` varsInBase (f $ Error "dummy")
varsInBase (Mixture _ es) = unions (map varsIn es)
varsInBase (Error_ _)     = S.empty
                                   
initEnv :: Term a -> Env
initEnv term = Env (Names 0 (varsIn term)) []

