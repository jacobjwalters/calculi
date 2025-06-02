||| Intrinsically scoped simply-typed lambda calculus.
module STLC.IntrinsicallyScoped.Core

import Data.List
import Data.SnocList
import Data.SnocList.Elem

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

public export
Name : Type
Name = String

public export
data Ty : Type where
  Base : Ty
  Fn : Ty -> Ty -> Ty

public export
Scope : Type
Scope = SnocList Name

public export
data Convertible : Ty -> Ty -> Type where
  BaseConv : Convertible Base Base
  FnConv : Convertible a1 a2 -> Convertible r1 r2 -> Convertible (Fn a1 r1) (Fn a2 r2)

public export
convertible : (a, b : Ty) -> Maybe $ Convertible a b
convertible Base Base = [| BaseConv |]
convertible (Fn a1 r1) (Fn a2 r2) = [| FnConv (convertible a1 a2) (convertible r1 r2) |]
convertible _ _ = Nothing

public export infixr 8 ~~
public export
(~~) : Ty -> Ty -> Bool
a ~~ b = maybe False (const True) $ convertible a b

public export
data Term : Scope -> Type where
  Var : (n : Name) -> (n `Elem` ctx) -> Term ctx
  Lam : (n : Name) -> Ty -> Term (ctx :< n) -> Term ctx
  App : Term ctx -> Term ctx -> Term ctx

public export
Context : Type
Context = SnocList (Name, Ty)

public export
synth : Context -> Term ctx -> Maybe Ty
synth g (Var n _) = lookup n $ asList g
synth g (Lam n t b) = Just $ Fn t !(synth (g :< (n, t)) b)
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

public export
check : Context -> Term ctx -> Ty -> Bool
check g e t = maybe False (t ~~) $ synth g e
