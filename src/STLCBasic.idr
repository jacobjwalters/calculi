module STLCBasic

import Data.List
import Data.SnocList
import Data.SnocList.Elem

import Text.Lexer
import Flap.Parser
import Flap.Data.Context
import Flap.Data.Context.Var
import Flap.Data.SnocList.Thinning

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)  -- conflicts with our conv relation

{-
Basic simply-typed lambda calculus.
No intrinsic scoping or typing.
-}

Name : Type
Name = String

data Ty : Type where
  Base : Ty
  Fn : Ty -> Ty -> Ty

data Convertible : Ty -> Ty -> Type where
  BaseConv : Convertible Base Base
  FnConv : Convertible a1 a2 -> Convertible r1 r2 -> Convertible (Fn a1 r1) (Fn a2 r2)

convertible : (a, b : Ty) -> Maybe $ Convertible a b
convertible Base Base = Just BaseConv
convertible (Fn a1 r1) (Fn a2 r2) = Just $ FnConv !(convertible a1 a2) !(convertible r1 r2)
convertible _ _ = Nothing

export infixr 8 ~~
(~~) : Ty -> Ty -> Bool
a ~~ b = case convertible a b of
              Nothing => False
              Just _  => True

data Term : Type where
  EVar : Name -> Term
  Lam : Name -> Ty -> Term -> Term
  App : Term -> Term -> Term

Context = SnocList (Name, Ty)

synth : Context -> Term -> Maybe Ty
synth g (EVar n) = lookup n $ asList g
synth g (Lam n t b) = Just $ Fn t !(synth (g :< (n, t)) b)
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

check : Context -> Term -> Ty -> Bool
check g e t = case synth g e of
                   Nothing => False
                   Just t' => t ~~ t'

-- LEXER --

data STLCToken : Type where
  LB, RB, Lambda, Colon, BaseT, Arrow, Dot, Identifier, Space : STLCToken

TokenKind STLCToken where
  TokType Identifier = String
  TokType LB     = ()
  TokType RB     = ()
  TokType Lambda = ()
  TokType Colon  = ()
  TokType BaseT  = Ty
  TokType Arrow  = ()
  TokType Dot    = ()
  TokType Space  = ()

  tokValue Identifier s = s
  tokValue LB     _ = ()
  tokValue RB     _ = ()
  tokValue Lambda _ = ()
  tokValue Colon  _ = ()
  tokValue BaseT  _ = Base
  tokValue Arrow  _ = ()
  tokValue Dot    _ = ()
  tokValue Space  _ = ()

Eq STLCToken where
  Identifier == Identifier = True
  LB == LB = True
  RB == RB = True
  Lambda == Lambda = True
  Colon == Colon = True
  BaseT == BaseT = True
  Arrow == Arrow = True
  Dot == Dot = True
  Space == Space = True
  _ == _ = False

Interpolation STLCToken where
  interpolate LB = "("
  interpolate RB = ")"
  interpolate Lambda = "Lambda"
  interpolate Colon = "Colon"
  interpolate BaseT = "Base"
  interpolate Arrow = "Arrow"
  interpolate Dot = "Dot"
  interpolate Identifier = "Id"
  interpolate Space = "Space"

tokenMap : TokenMap (Token STLCToken)
tokenMap = toTokenMap
  [ (is '(',  LB)
  , (is ')',  RB)
  , (is '\\', Lambda)
  , (is ':',  Colon)
  , (exact "Base", BaseT)
  , (exact "->",   Arrow)
  , (is '.',  Dot)
  , (alphaNums, Identifier)
  , (space <|> newline, Space)
  ]

-- PARSER --
reduceLeft : (a, List (a -> a -> a, a)) -> a
reduceLeft (hd, rest) = foldl (\acc, (op, arg) => op acc arg) hd rest

TyParser : SnocList String -> Type
TyParser locked = Parser Void STLCToken False (map (:- (False, Ty)) locked) [<] Ty

TermParser : SnocList String -> Type
TermParser locked = Parser Void STLCToken False (map (:- (False, Term)) locked) [<] Term

ty : TyParser [<]
ty = Fix "ty" fn
  where
    atomicTy : TyParser [<"ty"]
    atomicTy = OneOf [match BaseT, enclose (match LB) (match RB) (Var $ %%%"ty")]

    fn : TyParser [<"ty"]
    fn = foldr1 Fn <$> sepBy1 (match Arrow) atomicTy

brackets, var : TermParser [<"term"]
brackets = enclose (match LB) (match RB) (Var $ %%%"term")
var = EVar <$> match Identifier

atomic : TermParser [<"term"]
atomic = OneOf [brackets, var]

app : TermParser [<"term"]
app = (foldl1 App) <$> plus atomic

lambda : TermParser [<"term"]
lambda = (\[_, x, _, t, _, b] => Lam x t b) <$> Seq [match Lambda, match Identifier, match Colon, rename Id (Drop Id) ty, match Dot, Var $ %%%"term"]

term : TermParser [<]
term = Fix "term" $ OneOf [app, lambda]

filterSpaces : List (WithBounds (Token STLCToken))
            -> List (WithBounds (Token STLCToken))
filterSpaces = filter (\x => x.val.kind /= Space)

[SetImp] Eq a => Set a (List a) where
  toList = id
  intersect xs ys = filter (`elem` xs) ys
  member = elem
  singleton = List.singleton

%hint
parserOk : WellFormed SetImp STLCBasic.term
parserOk = Refl

partial
parseSTLC : String -> Term
parseSTLC str =
  let tokens = filterSpaces $ fst (lex tokenMap str) in
  case (parse SetImp term).runParser () tokens of
    (Ok res ys prf) => res
    (SoftErr errs ys prf) => idris_crash $ "parse error"
    (Err errs) => idris_crash $ "parse error"

-- EXAMPLES --
Ex_base_id : Term
Ex_base_id = Lam "x" Base (EVar "x")

Ex_check_base_id : check [<] Ex_base_id (Fn Base Base) = True
Ex_check_base_id = Refl

Ex_ill_scoped1 : Term
Ex_ill_scoped1 = Lam "x" Base (EVar "y")

Ex_ill_scoped2 : Term
Ex_ill_scoped2 = Lam "x" Base (EVar "x")

Ex_ill_typed : Term
Ex_ill_typed = Lam "x" (Fn Base Base) (EVar "x")
