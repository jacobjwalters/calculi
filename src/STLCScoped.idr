module STLCScoped

import Data.List
import Data.SnocList
import Data.SnocList.Elem

%hide Syntax.PreorderReasoning.Ops.infixl.(~~)

{-
Intrinsically scoped simply-typed lambda calculus.
-}

Name : Type
Name = String
  
Scope : Type
Scope = SnocList Name

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

data Term : Scope -> Type where
  Var : (n : Name) -> (n `Elem` ctx) -> Term ctx
  Lam : (n : Name) -> Ty -> Term (ctx :< n) -> Term ctx
  App : Term ctx -> Term ctx -> Term ctx

Context = SnocList (Name, Ty)

synth : Context -> Term ctx -> Maybe Ty
synth g (Var n _) = lookup n $ asList g
synth g (Lam n t b) = synth (g :< (n, t)) b
synth g (App f a) = case (synth g f, synth g a) of
                         (Just $ Fn a1 r, Just a) => if a1 ~~ a then Just a else Nothing
                         _                        => Nothing

check : Context -> Term ctx -> Ty -> Bool
check g e t = case synth g e of
                   Nothing => False
                   Just t' => t ~~ t'

ex1 : Term [<]
ex1 = Lam "x" Base (Var "x" Here)

failing
  ex2 : Term [<]
  ex2 = Lam "x" Base (Var "y" Here)

