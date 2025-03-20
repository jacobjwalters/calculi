||| Parser definitions for the basic STLC core.
module STLC.Basic.Parser

import Data.List
import Text.Lexer
import Flap.Parser
import Flap.Data.Context
import Flap.Data.Context.Var
import Flap.Data.SnocList.Thinning

import STLC.Basic.Core

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
0
parserOk : WellFormed SetImp Parser.term
parserOk = Refl

partial public export
parseSTLC : String -> Term
parseSTLC str =
  let tokens = filterSpaces $ fst (lex tokenMap str) in
  case (parse SetImp term).runParser () tokens of
    (Ok res ys prf) => res
    (SoftErr errs ys prf) => idris_crash $ "parse error"
    (Err errs) => idris_crash $ "parse error"
