||| Basic simply-typed lambda calculus.
||| No intrinsic scoping or typing.
module STLC.Basic.Core

import Data.List
import public Data.SnocList

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)  -- conflicts with our conv relation

public export
Name : Type
Name = String

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
a ~~ b = maybe False (const True) $ convertible a b

public export
data Term : Type where
  EVar : Name -> Term
  Lam : Name -> Ty -> Term -> Term
  App : Term -> Term -> Term

public export
Context : Type
Context = SnocList (Name, Ty)

public export
synth : Context -> Term -> Maybe Ty
synth g (EVar n) = lookup n $ asList g
synth g (Lam n t b) = Just $ Fn t !(synth (g :< (n, t)) b)
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

public export
check : Context -> Term -> Ty -> Bool
check g e t = maybe False (t ~~) $ synth g e
