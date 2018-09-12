{-# LANGUAGE CPP, 
             GADTs, 
             TypeSynonymInstances, 
             FlexibleInstances,
             MultiParamTypeClasses #-}

module Pretty where

import           Syntax
import           Text.PrettyPrint hiding (parens, empty, rational)
import qualified Text.PrettyPrint as PP (parens, empty, rational)
import           Control.Monad.State.Lazy (MonadState(..), StateT(..))
import           Data.Graph.Inductive (Node, LNode, LEdge, Gr, mkGraph)
import           Data.GraphViz hiding (Int, Square)
import           Data.GraphViz.Printing (renderDot)
import           Data.GraphViz.Attributes.Complete hiding (Int,Square,Normal)
import           Data.Text.Lazy (Text, pack, unpack)
import           Control.Monad.State.Lazy (State, execState)
import           Control.Monad (liftM)
-- import           Debug.Trace

track :: (Pretty a, Pretty h, Pretty b, Pretty t)
      => String -> (a, h, Maybe b, Maybe t) -> D c -> D c
track str (a,heap,mb,mt) d =
    do env <- get
       let onestep = text str <+> (braces (pretty a) $$
                                   maybe PP.empty pretty mb $$
                                   maybe PP.empty pretty mt $$
                                   pretty heap)
           tr      = runDisintegrate d env
#ifdef TRACE
       -- traceShow onestep $ 
       StateT (\_ -> Step onestep tr)
#else
       StateT (\_ -> tr)
#endif

parens :: Bool -> Doc -> Doc
parens True  d = PP.parens (nest 1 d)
parens False d = d

ppFun :: Int -> String -> [Doc] -> Doc
ppFun _ f [] = text f
ppFun p f ds =
    parens (p > 9) (text f <+> nest (1 + length f) (sep ds))

data Associativity = LeftAssoc | RightAssoc | NonAssoc

ppBinop :: (Pretty a, Pretty b)
        => String -> Int -> Associativity
        -> Int -> a -> b -> Doc
ppBinop op p0 assoc =
    let (p1,p2) =
            case assoc of
            LeftAssoc  -> (p0, 1 + p0)
            RightAssoc -> (1 + p0, p0)
            NonAssoc   -> (1 + p0, 1 + p0)
    in \p e1 e2 -> 
        parens (p > p0) $
        sep [ pp p1 e1 , text op <+> pp p2 e2 ]

ppArg :: (Pretty a) => a -> Doc
ppArg = pp 11         
                   
pretty :: (Pretty a) => a -> Doc
pretty = pp 0

class Pretty a where
    pp :: Int -> a -> Doc

instance Pretty Doc where
    pp _ = id
          
instance Pretty Var where
    pp _ = text . name

instance Pretty BVar where
    pp _ = text . name_

instance (Pretty v) => Pretty (Guard v) where
    pp _ (x :<~ m)     = pretty x <+> text "<~" <+> pretty m
    pp p (Factor f)    = ppFun p "factor" [ppArg f]
    pp p (LetInl x e)  = parens (p > 5) $ text "let inl" <+>
                         pretty x <+> text "=" <+> ppArg e
    pp p (LetInr x e)  = parens (p > 5) $ text "let inr" <+>
                         pretty x <+> text "=" <+> ppArg e
    pp p (Divide b b' t) = ppFun p "divide" [ppArg b, ppArg b', ppArg t]

instance Pretty (Term a) where
    pp _ Pi       = text "π"
    pp _ (Real r) = PP.rational r
    pp p (Neg e)  = ppFun p "neg" [ppArg e]
    pp p (Abs e)  = ppFun p "abs" [ppArg e]
    pp p (Recip e)  = ppFun p "recip" [ppArg e]
    pp p (Exp e)  = ppFun p "exp" [ppArg e]
    pp p (Log e)  = ppFun p "log" [ppArg e]
    pp p (Sqrt e)    = ppFun p "sqrt" [ppArg e]
    pp p (Square e)  = ppBinop "^" 8 RightAssoc p e (Real 2)
    pp p (Add e1 e2) = ppBinop "+" 7 LeftAssoc p e1 e2
    pp p (Mul e1 e2) = ppBinop "*" 8 LeftAssoc p e1 e2
    pp p (Inl e) = ppFun p "inl" [ppArg e]
    pp p (Inr e) = ppFun p "inr" [ppArg e]
    -- pp T = text "true"
    -- pp F = text "false"
    pp p (Equal e1 e2) = ppBinop "==" 4 NonAssoc p e1 e2
    pp p (Less e1 e2) =  ppBinop "<" 4 NonAssoc p e1 e2
    -- pp (Not e) = text "not" <+> PP.parens (pp e)
    pp p (Or  e1 e2) = ppBinop "||" 4 NonAssoc p e1 e2
    -- pp (And e1 e2) = text "and" <+> (PP.parens (pp e1) $$ PP.parens (pp e2))
    pp _ Unit = text "unit"
    pp _ (Pair e1 e2) = pretty (e1,e2)
    pp p (Fst e) = ppFun p "fst" [ppArg e]
    pp p (Snd e) = ppFun p "snd" [ppArg e]
    pp p (If c t e) = ppFun p "if" [ppArg c, ppArg t, ppArg e]
    pp _ Fail = text "fail"
    pp _ Lebesgue = text "lebesgue"
    pp p (Dirac e)      = ppFun p "dirac" [ppArg e]
    pp p (Normal mu sd) = ppFun p "normal" [ppArg mu, ppArg sd]
    pp p (Do g m) = parens (p > 5) $ vcat [pretty g <> semi, pretty m]
    pp p (MPlus m1 m2) = ppFun p "mplus" [ppArg m1, ppArg m2]
    pp _ (Var v) = pretty v
    pp p (Jacobian f b t) = ppFun p "jacobian" [ppArg f, ppArg b, ppArg t]
    pp _ (Error e) = sep [text "err:", text e]

ppLam :: Int -> Term a -> Base b -> Doc
ppLam p x body = parens (p > 9) $
                 text "λ" <> pretty x <> text "." <+> pretty body -- (f x)

instance Pretty (Base a) where
    pp _ (Var_ v es)   = pretty v <> text "_" <> pretty es
    pp p (LiftB f b)   = ppFun p "liftB"  [ppArg f, ppArg b]
    pp p (Dirac_ e)    = ppFun p "dirac_" [ppArg e]
    pp _ Lebesgue_     = text "lebesgue_"
    pp p (Either b b') = ppFun p "either" [ppArg b, ppArg b']
    pp p e@(Bindx b f) = let (str,_) = freshName "x" (Names 0 (varsInBase e))
                             x = Var (V str)
                         in ppFun p "bindx" [ppArg b, ppLam 11 x (f x)]
    pp p (Mixture b es) = ppFun p "mixture" [ppArg b, ppArg es]
    pp _ (Error_ msg)    = sep [text "err_:", text msg]

instance Pretty Invertible where
    pp _ Id_        = text "id_"
    pp _ Neg_       = text "neg_"
    pp _ Abs_Pos    = text "abs_⁺"
    pp _ Abs_Neg    = text "abs_⁻"
    pp _ Recip_     = text "recip"
    pp p (Add_ e)   = ppFun p "add_" [ppArg e]
    pp p (Sub_ e)   = ppFun p "sub_" [ppArg e]
    pp p (Mul_ e)   = ppFun p "mul_" [ppArg e]
    pp p (Div_ e)   = ppFun p "div_" [ppArg e]
    pp _ Exp_       = text "exp_"
    pp _ Log_       = text "log_"
    pp _ Square_Pos = text "square_⁺"
    pp _ Square_Neg = text "square_⁻"
    pp _ Sqrt_Pos   = text "sqrt_⁺"
    pp _ Sqrt_Neg   = text "sqrt_⁻"

instance Pretty Bool where
    pp _ True  = text "true"
    pp _ False = text "false"   

instance (Pretty a, Pretty b) => Pretty (a,b) where
    pp _ (a,b) = parens True $ sep [pretty a <> comma, pretty b]

ppList :: (Pretty a) => [a] -> Doc
ppList = brackets . fsep . punctuate comma . map pretty

instance Pretty [Term a] where
    pp _ = ppList

instance Pretty Heap where
    pp _ = brackets . fsep . punctuate semi . map pretty

instance Pretty Constraint where
    pp p (e1 :<: e2) = ppBinop "<:" 4 NonAssoc p e1 e2

instance Pretty [Constraint] where
    pp _ = ppList

instance Pretty [[Constraint]] where
    pp _ = ppList           

instance Pretty InScope where
    pp p (IS t) = pp p t

instance Pretty [InScope] where
    pp _ = ppList

instance (Pretty a) => Pretty (Trace a) where
    pp _ Bot         = text "⊥"
    pp _ (Return a)  = pretty a
    pp _ (Step d t)  = (text ">" <+> d) $$ pretty t
    pp _ (Lub t1 t2) = nest 4 (pretty t1) $+$
                       nest 1 (text "⊔") $+$
                       nest 4 (pretty t2)

instance Show (Term a) where
    show = render . pretty

instance (Pretty a) => Show (Guard a) where
    show = render . pretty

instance Show (Base a) where
    show = render . pretty

instance Show Constraint where
    show = render . pretty

instance (Pretty a) => Show (Trace a) where
    show = render . pretty

instance Show Var where
    show = render . pretty

instance Show InScope where
    show = render . pretty

instance Show BVar where
    show = render . pretty

class (Pretty t, Pretty c) => Displayable t c where
    display :: Trace (t,c) -> Trace Doc

result :: (Pretty a, Pretty b) => a -> String -> b -> Doc
result a msg b = pretty a $+$ text msg $+$ pretty b

instance Displayable (Term a) [Constraint] where
    display anss = fmap ppOutput anss
        where ppOutput (t, cs) = result t "--under the constraints--" cs

instance Displayable (Term a) (Base b) where
    display anss = fmap ppOutput anss
        where ppOutput (t, b) = result t "--with respect to--" b
                                

-- | Trace graphs --------------------------------------------------------------

data Structure = S { curr  :: Node
                   , nodes :: [LNode Text]
                   , edges :: [LEdge ()] }

gen :: State Structure Node
gen = do s <- get
         let n = curr s + 1
         put (s {curr = n}) >> return n

grow :: LNode Text -> State Structure ()
grow n = do s <- get
            put (s {nodes = n : nodes s})

connect :: LEdge () -> State Structure ()
connect e = do s <- get
               put (s {edges = e : edges s})

packL :: String -> Text
packL = pack . (++ "\\l") . concatMap (\c -> if c=='\n' then "\\l" else [c])
        
learn :: (Show a) => Trace a -> State Structure ()
learn Bot         = do n <- liftM curr get
                       grow (n, pack "⊥")
learn (Return t)  = do n <- liftM curr get
                       grow (n, packL (show t))
learn (Step d t)  = do m <- liftM curr get
                       grow (m, packL (render d))
                       n <- gen
                       connect (m,n, ()) >> learn t
learn (Lub t1 t2) = do n <- liftM curr get
                       grow (n, pack "⊔")
                       n1 <- gen
                       connect (n,n1,()) >> learn t1
                       n2 <- gen
                       connect (n,n2,()) >> learn t2
                         
traceToGraph :: (Show a) => Trace a -> Gr Text ()
traceToGraph tr = mkGraph nds edgs
    where initial        = S 0 [] []
          (S _ nds edgs) = execState (learn tr) initial

params :: Text -> GraphvizParams Node Text () () Text
params title
    = nonClusteredParams {
        globalAttributes = [ GraphAttrs [ Label (StrLabel title)
                                        , LabelLoc VTop
                                        , LabelJust JLeft
                                        , FontName (pack "Courier")
                                        , FontSize 28 ]
                           , NodeAttrs [Shape BoxShape] ]
      , fmtNode = \(_,l) -> [ Label (StrLabel l)
                            , FontName (pack "Courier") ]
      }

traceToDot :: (Show a) => Doc -> Trace a -> String
traceToDot title = unpack . renderDot . toDot .
                   graphToDot (params $ packL $ show title) .
                   traceToGraph
