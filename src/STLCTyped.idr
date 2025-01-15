module STLCTyped

import Data.List
import Data.SnocList
import Data.SnocList.Elem

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

{-
Intrinsically scoped and typed simply-typed lambda calculus.
-}

Name : Type
Name = String
  
data Ty : Type where
  Base : Ty
  Fn : Ty -> Ty -> Ty

Scope : Type
Scope = SnocList (Name, Ty)

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

data Term : Scope -> Ty -> Type where
  Var : (n : Name) -> (ty : Ty) -> ((n, ty) `Elem` ctx) -> Term ctx ty
  Lam : (n : Name) -> (ty : Ty) -> Term (ctx :< (n, ty)) rty -> Term ctx (Fn ty rty)
  App : Term ctx (Fn ary rty) -> Term ctx ary -> Term ctx rty

Context = SnocList (Name, Ty)

synth : Context -> Term ctx ty -> Maybe Ty
synth g (Var n ty _) = Just ty
synth g (Lam n t b) = synth (g :< (n, t)) b
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

check : Context -> Term ctx ty -> Ty -> Bool
check g e t = case synth g e of
                   Nothing => False
                   Just t' => t ~~ t'

ex1 : Term [<] (Fn Base Base)
ex1 = Lam "x" Base (Var "x" Base Here)

failing
  Ex_ill_scoped1 : Term [<] Unit
  Ex_ill_scoped1 = Lam "x" Base (Var "y" Here)

  Ex_ill_scoped2 : Term [<] Unit
  Ex_ill_scoped2 = Lam "x" Base (Var "x" (There Here))

  Ex_ill_typed : Term [<]
  Ex_ill_typed = Lam "x" (Fn Base Base) (Var "x" Base Here)

  Ex_omega_ill_typed1 : Term [<] ?omega_ty_1
  Ex_omega_ill_typed1 = Lam "x" Base (App (Var "x" Base Here) (Var "x" Base Here))

  Ex_omega_ill_typed2 : Term [<] ?omega_ty_2
  Ex_omega_ill_typed2 = Lam "x" (Fn Base Base) (App (Var "x" (Fn Base Base) Here) (Var "x" (Fn Base Base) Here))
