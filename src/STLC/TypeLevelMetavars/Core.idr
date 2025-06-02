||| Intrinsically scoped STLC with type-level metavars (holes)
module STLC.TypeLevelMetavars.Core

import Data.List
import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Quantifiers
  
import Text.Lexer
import Flap.Parser
import Flap.Data.Context
import Flap.Data.Context.Var
import Flap.Data.SnocList.Thinning

%hide Flap.Data.Context.Context  -- conflicts with ?tymv

%default total

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

public export
0
ForAll : (xs : SnocList a) -> (0 p : a -> Type) -> Type
ForAll xs p = All p xs

public export
Name : Type
Name = String

public export
Scope : Type
Scope = SnocList Name

public export
TyFam : Type
TyFam = Type

public export
data Ty : (tymv : TyFam) -> Type where
  Base : Ty tymv
  Fn : Ty tymv -> Ty tymv -> Ty tymv
  MV : tymv -> Ty tymv

public export
data Convertible : Ty tymv -> Ty tymv -> Type where
  BaseConv : Convertible Base Base
  FnConv : Convertible a1 a2 -> Convertible r1 r2 -> Convertible (Fn a1 r1) (Fn a2 r2)
  DelayedL : Convertible (MV mv) t
  DelayedR : Convertible t (MV mv)

public export
convertible : (a, b : Ty tymv) -> Maybe $ Convertible a b
convertible Base Base = Just BaseConv
convertible (Fn a1 r1) (Fn a2 r2) = Just $ FnConv !(convertible a1 a2) !(convertible r1 r2)
convertible (MV _) _ = Just DelayedL
convertible _ (MV _) = Just DelayedR
convertible _ _ = Nothing

public export infixr 8 ~~
public export
(~~) : Ty tymv -> Ty tymv -> Bool
a ~~ b = maybe False (const True) $ convertible a b

public export
data Term : Scope -> (tymv : TyFam) -> Type where
  Var : (n : Name) -> (n `Elem` ctx) -> Term ctx tymv
  Lam : (n : Name) -> Ty tymv -> Term (ctx :< n) tymv -> Term ctx tymv
  App : Term ctx tymv -> Term ctx tymv -> Term ctx tymv

public export
Context : (tymv : TyFam) -> Type
Context tymv = SnocList (Name, Ty tymv)

public export
synth : Context tymv -> Term ctx tymv -> Maybe (Ty tymv)
synth g (Var n _) = lookup n $ asList g
synth g (Lam n t b) = Just $ Fn t !(synth (g :< (n, t)) b)
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

public export
check : Context tymv -> Term ctx tymv -> Ty tymv -> Bool
check g e t = maybe False (t ~~) $ synth g e
