||| Intrinsically scoped and typed simply-typed lambda calculus.
module STLC.IntrinsicallyTyped.Core

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
Scope = SnocList (Name, Ty)

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
a ~~ b = maybe False (const True) $ convertible a b

public export
data Term : Scope -> Ty -> Type where
  Var : (n : Name) -> (ty : Ty) -> ((n, ty) `Elem` ctx) -> Term ctx ty
  Lam : (n : Name) -> (ty : Ty) -> Term (ctx :< (n, ty)) rty -> Term ctx (Fn ty rty)
  App : Term ctx (Fn ary rty) -> Term ctx ary -> Term ctx rty

public export
Context : Type
Context = SnocList (Name, Ty)

public export
synth : Context -> Term ctx ty -> Maybe Ty
synth g (Var n ty _) = Just ty
synth g (Lam n t b) = synth (g :< (n, t)) b
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

public export
check : Context -> Term ctx ty -> Ty -> Bool
check g e t = maybe False (t ~~) $ synth g e
