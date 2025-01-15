module STLCScopedMTyVar

import Data.List
import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Quantifiers

%default total

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

0
ForAll : (xs : SnocList a) -> (0 p : a -> Type) -> Type
ForAll xs p = All p xs

{-
Intrinsically scoped simply-typed lambda calculus with metavariables in the type system.
-}

Name : Type
Name = String

Scope : Type
Scope = SnocList Name

TyFam : Type
TyFam = Type

data Ty : (tymv : TyFam) -> Type where
  Base : Ty tymv
  Fn : Ty tymv -> Ty tymv -> Ty tymv
  MV : tymv -> Ty tymv

data Convertible : Ty tymv -> Ty tymv -> Type where
  BaseConv : Convertible Base Base
  FnConv : Convertible a1 a2 -> Convertible r1 r2 -> Convertible (Fn a1 r1) (Fn a2 r2)
  DelayedL : Convertible (MV mv) t
  DelayedR : Convertible t (MV mv)

convertible : (a, b : Ty tymv) -> Maybe $ Convertible a b
convertible Base Base = Just BaseConv
convertible (Fn a1 r1) (Fn a2 r2) = Just $ FnConv !(convertible a1 a2) !(convertible r1 r2)
convertible (MV _) _ = Just DelayedL
convertible _ (MV _) = Just DelayedR
convertible _ _ = Nothing

export infixr 8 ~~
(~~) : Ty tymv -> Ty tymv -> Bool
a ~~ b = case convertible a b of
              Nothing => False
              Just _  => True

data Term : Scope -> (tymv : TyFam) -> Type where
  Var : (n : Name) -> (n `Elem` ctx) -> Term ctx tymv
  Lam : (n : Name) -> Ty tymv -> Term (ctx :< n) tymv -> Term ctx tymv
  App : Term ctx tymv -> Term ctx tymv -> Term ctx tymv

Context : (tymv : TyFam) -> Type
Context tymv = SnocList (Name, Ty tymv)

synth : Context tymv -> Term ctx tymv -> Maybe (Ty tymv)
synth g (Var n _) = lookup n $ asList g
synth g (Lam n t b) = Just $ Fn t !(synth (g :< (n, t)) b)
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

check : Context tymv -> Term ctx tymv -> Ty tymv -> Bool
check g e t = case synth g e of
                   Nothing => False
                   Just t' => t ~~ t'

Ex_base_id : Term [<] Unit
Ex_base_id = Lam "x" Base (Var "x" Here)

Ex_check_base_id : check [<] Ex_base_id (Fn Base Base) = True
Ex_check_base_id = Refl

Ex_mv_str_id : Term [<] String
Ex_mv_str_id = Lam "x" (MV "idty") (Var "x" Here)

Ex_check_mv_str_id : check [<] Ex_mv_str_id (Fn Base Base) = True
Ex_check_mv_str_id = Refl

Ex_ill_typed : Term [<] Unit
Ex_ill_typed = Lam "x" (Fn Base Base) (Var "x" Here)

failing
  Ex_ill_scoped1 : Term [<] Unit
  Ex_ill_scoped1 = Lam "x" Base (Var "y" Here)

  Ex_ill_scoped2 : Term [<] Unit
  Ex_ill_scoped2 = Lam "x" Base (Var "x" (There Here))
