||| Intrinsically scoped simply-typed lambda calculus with term-level metavariables.
module STLC.TermLevelMetavars.Core

import Data.List
import Data.SnocList
import Data.SnocList.Elem

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

public export
Name : Type
Name = String

public export
Scope : Type
Scope = SnocList Name

public export
Fam : Type
Fam = Type

public export
data Ty : Type where
  Base : Ty
  Fn : Ty -> Ty -> Ty

public export
data Convertible : Ty -> Ty -> Type where
  BaseConv : Convertible Base Base
  FnConv : Convertible a1 a2 -> Convertible r1 r2 -> Convertible (Fn a1 r1) (Fn a2 r2)

public export
convertible : (a, b : Ty) -> Maybe $ Convertible a b
convertible Base Base = Just BaseConv
convertible (Fn a1 r1) (Fn a2 r2) = Just $ FnConv !(convertible a1 a2) !(convertible r1 r2)
convertible _ _ = Nothing

public export infixr 8 ~~
public export
(~~) : Ty -> Ty -> Bool
a ~~ b = case convertible a b of
              Nothing => False
              Just _  => True

public export
data Term : (temv : Fam) -> Scope -> Type where
  Var : (n : Name) -> (n `Elem` ctx) -> Term temv ctx
  Lam : (n : Name) -> Ty -> Term temv (ctx :< n) -> Term temv ctx
  App : Term temv ctx -> Term temv ctx -> Term temv ctx
  MVar : temv -> Term temv ctx

public export
Context : Type
Context = SnocList (Name, Ty)

public export
synth : Context -> Term temv ctx -> Maybe Ty
synth g (Var n _) = lookup n $ asList g
synth g (Lam n t b) = Just $ Fn t !(synth (g :< (n, t)) b)
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing
synth g (MVar v) = ?rh_3

public export
check : Context -> Term temv ctx -> Ty -> Bool
check g e t = maybe False (t ~~) $ synth g e
