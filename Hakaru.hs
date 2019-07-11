{-# LANGUAGE DataKinds,
             KindSignatures,
             TypeFamilies,
             TypeOperators #-}

module Hakaru where

import qualified Language.Hakaru.Syntax.ABT as ABT
import qualified Language.Hakaru.Syntax.AST as AST
import qualified Language.Hakaru.Syntax.Datum as SD
import qualified Language.Hakaru.Syntax.Prelude as HP
import qualified Language.Hakaru.Syntax.Variable as SV
import qualified Language.Hakaru.Types.DataKind as DK
import qualified Language.Hakaru.Types.Sing as TS
import qualified Language.Hakaru.Types.HClasses as HC
import qualified Language.Hakaru.Pretty.Concrete as PC
import qualified Data.Text as Text
import qualified Data.Number.Nat as NN
import qualified Control.Monad as CM
import qualified Control.Monad.State as S
import Helpers
import Tests    
import Unsafe.Coerce (unsafeCoerce)

import Syntax

class HakaruType (a :: H) where
    type HType a :: DK.Hakaru

instance HakaruType HUnit where
    type HType HUnit = DK.HUnit

instance HakaruType HReal where
    type HType HReal = DK.HReal

instance (HakaruType a, HakaruType b, TS.SingI a, TS.SingI b) => HakaruType (HEither a b) where
    type HType (HEither a b) = DK.HEither (HType a) (HType b)

instance (HakaruType a, HakaruType b) => HakaruType (HPair a b) where
    type HType (HPair a b) = DK.HPair (HType a) (HType b)

instance (HakaruType a) => HakaruType (HMeasure a) where
    type HType (HMeasure a) = DK.HMeasure (HType a)

toHSing :: Type (a :: H) -> TS.Sing (HType a)
toHSing TUnit = TS.sUnit
toHSing TReal = TS.SReal
toHSing (TEither t1 t2) = TS.sEither (toHSing t1) (toHSing t2)
toHSing (TPair t1 t2) = TS.sPair (toHSing t1) (toHSing t2)
toHSing (TMeasure t) = TS.SMeasure (toHSing t)

type HakaruTerm a = ABT.TrivialABT AST.Term '[] a
type VarIDMap = [(Var, NN.Nat)]

nextID :: VarIDMap -> NN.Nat
nextID [] = 0
nextID vm = maximum (map snd vm) + 1

toHakaru :: Term a -> S.State VarIDMap (HakaruTerm (HType a))
toHakaru Pi = return HP.pi
toHakaru (Real r) = return $ HP.real_ r
toHakaru (Neg e) = HP.negate <$> (toHakaru e)
toHakaru (Abs e) = HP.abs <$> toHakaru e
toHakaru (Recip e) = HP.recip <$> toHakaru e
toHakaru (Exp e) = HP.fromProb . HP.exp <$> toHakaru e
toHakaru (Log e) = HP.log . HP.unsafeProb <$> toHakaru e
toHakaru (Sqrt e) = HP.fromProb . HP.sqrt . HP.unsafeProb <$> toHakaru e
toHakaru (Square e) = HP.fromProb . HP.square <$> toHakaru e
toHakaru (Add e e') = CM.liftM2 (HP.+) (toHakaru e) (toHakaru e')
toHakaru (Mul e e') = CM.liftM2 (HP.*) (toHakaru e) (toHakaru e')
toHakaru t@(Inl e) = let (sa,sb) = TS.sUnEither (toHSing $ typeOf t)
                     in HP.datum_ . SD.dLeft_ sa sb <$> toHakaru e
toHakaru t@(Inr e) = let (sa,sb) = TS.sUnEither (toHSing $ typeOf t)
                     in HP.datum_ . SD.dRight_ sa sb <$> toHakaru e
toHakaru (Equal e e') =
    case (HC.hEq_Sing $ toHSing (typeOf e)) of
      Just heq -> boolToUnit <$> CM.liftM2 (HP.primOp2_ (AST.Equal heq))
                                           (toHakaru e)
                                           (toHakaru e')
      Nothing -> error $ "toHakaru: no defn of hEq"
toHakaru (Or e e') = boolToUnit <$> CM.liftM2 (HP.||) (toHakaruBool e) (toHakaruBool e')
toHakaru Unit = return HP.unit
toHakaru t@(Pair e e') = let (sa,sb) = TS.sUnPair (toHSing $ typeOf t)
                         in CM.liftM2 (HP.pair_ sa sb) (toHakaru e) (toHakaru e')
toHakaru (Fst e) = HP.fst <$> toHakaru e
toHakaru (Snd e) = HP.snd <$> toHakaru e
toHakaru (If b e e') = CM.liftM3 (HP.if_) (toHakaruBool b) (toHakaru e) (toHakaru e')
toHakaru t@Fail = return $ HP.reject (toHSing $ typeOf t)
toHakaru Lebesgue = return HP.lebesgue
toHakaru (Dirac e) = HP.dirac <$> toHakaru e
toHakaru (Normal m s) = CM.liftM2 (HP.normal) (toHakaru m) (HP.unsafeProb <$> toHakaru s)
toHakaru (Do (x :<~ m) m') = hakaruBind x m m' $ \n hm hm' ->
                             let v = SV.Variable (Text.pack (name x)) n $
                                     TS.sUnMeasure (toHSing (typeOf m))
                             in ABT.syn (AST.MBind AST.:$ hm
                                                   AST.:* ABT.bind v hm'
                                                   AST.:* AST.End) 
toHakaru (Do (Factor e) m) = CM.liftM2 HP.withWeight (HP.unsafeProb <$> toHakaru e) (toHakaru m)
toHakaru (Do (LetInl x e) m) = hakaruBind x e m $ \n he hm ->
                               let t = TS.sUnEither (toHSing (typeOf e))
                                   h = Text.pack (name x)
                                   vlft = SV.Variable h n (fst t)
                                   vrgt = SV.Variable h n (snd t)
                               in ABT.syn $ AST.Case_ he $
                                  [ SD.Branch (SD.pLeft  SD.PVar) (ABT.bind vlft hm)
                                  , SD.Branch (SD.pRight SD.PVar) (ABT.bind vrgt $ HP.reject (toHSing (typeOf m))) ]
toHakaru (Do (LetInr x e) m) = hakaruBind x e m $ \n he hm ->
                               let t = TS.sUnEither (toHSing (typeOf e))
                                   h = Text.pack (name x)
                                   vlft = SV.Variable h n (fst t)
                                   vrgt = SV.Variable h n (snd t)
                               in ABT.syn $ AST.Case_ he $
                                  [ SD.Branch (SD.pLeft  SD.PVar) (ABT.bind vlft $ HP.reject (toHSing (typeOf m)))
                                  , SD.Branch (SD.pRight SD.PVar) (ABT.bind vrgt hm) ]                          
toHakaru (Do (Divide _ _ _) _) = error "toHakaru: no defn for Divide guard"
toHakaru (MPlus m m') = CM.liftM2 (HP.<|>) (toHakaru m) (toHakaru m')
toHakaru t@(Var v) = do vm <- S.get
                        let id = case lookup v vm of
                                   Just n -> n
                                   Nothing -> nextID vm
                        return $ ABT.var $ SV.Variable (Text.pack (name v)) id (toHSing (typeOf t))
toHakaru (Jacobian _ _ _) = error "toHakaru: no defn for Jacobian"
toHakaru (Error _) = error "toHakaru: no defn for Error"
toHakaru e = error ("toHakaru: unknown term " ++ show e)

toHakaruBool :: TermHBool -> S.State VarIDMap (HakaruTerm DK.HBool)
toHakaruBool (Inl Unit) = return HP.true
toHakaruBool (Inr Unit) = return HP.false
toHakaruBool e = do e' <- toHakaru e
                    return $ HP.if_ (e' HP.== HP.left HP.unit) HP.true HP.false

boolToUnit :: HakaruTerm DK.HBool -> HakaruTerm (DK.HEither DK.HUnit DK.HUnit)
boolToUnit e = HP.if_ e (HP.left HP.unit) (HP.right HP.unit)

hakaruBind :: Var
           -> Term a
           -> Term b
           -> (NN.Nat -> HakaruTerm (HType a) -> HakaruTerm (HType b) -> r)
           -> S.State VarIDMap r
hakaruBind x e e' c = do he <- toHakaru e
                         vm <- S.get
                         let id = case lookup x vm of
                                    Nothing -> nextID vm
                                    Just id -> id
                         S.put $ (x,id):vm
                         he' <- toHakaru e'
                         return $ c id he he'

translate :: Term a -> HakaruTerm (HType a)
translate t = S.evalState (toHakaru t) []

-- TODO: fix this. Currently wrong because there is a mismatch of
-- varIDs, between the "t" in the binding position and the "t"s in use
-- positions.
toHakaruLam :: TS.Sing a -> Term b -> HakaruTerm (a DK.:-> HType b)
toHakaruLam s e = let (e',vm) = S.runState (toHakaru e) []
                      obs = V "t"
                      v = SV.Variable (Text.pack (name obs)) (nextID vm) s
                  in ABT.syn (AST.Lam_ AST.:$ ABT.bind v e' AST.:* AST.End)

test :: IO ()
test = print $ PC.pretty (S.evalState (toHakaru helloWorld) [])
