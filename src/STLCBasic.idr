module STLCBasic

import Data.List
import Data.SnocList

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

{-
Basic simply-typed lambda calculus.
No intrinsic scoping or typing.
-}

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

infixr 8 ~~
(~~) : Ty -> Ty -> Bool
a ~~ b = case convertible a b of
              Nothing => False
              Just _  => True

data Term : Type where
  Var : Name -> Term
  Lam : Name -> Ty -> Term -> Term
  App : Term -> Term -> Term

Context = SnocList (Name, Ty)

synth : Context -> Term -> Maybe Ty
synth g (Var n) = lookup n $ asList g
synth g (Lam n t b) = synth (g :< (n, t)) b
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

check : Context -> Term -> Ty -> Bool
check g e t = case synth g e of
                   Nothing => False
                   Just t' => t ~~ t'
