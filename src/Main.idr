module Main

import Data.List
import Data.SnocList
import Data.SnocList.Elem
import Data.SnocList.Quantifiers

Name = String

0
ForAll : (xs : SnocList a) -> (0 p : a -> Type) -> Type
ForAll xs p = All p xs


{-
TODO/Questions:
How do I represent well-formed contexts? ( |- Gamma : Context ) It's not needed rn, but will be important as we extend the TT
Should Tau be replaced with something else? Named base types?
Can/should we do type checking without inference?
How long can we get away with TypeEq?
-}



Scope : Type
Scope = SnocList Name

TyFam : Type
TyFam = Type


data Ty : (tymv : TyFam) -> Type where
  Tau : Ty tymv
  Fn : Ty tymv -> Ty tymv -> Ty tymv
  MV : tymv -> Ty tymv
  
{-
Eq Ty where
  Tau == Tau = True
  (Fn t1 t2) == (Fn t1' t2') = t1 == t1' && t2 == t2'
  _ == _ = False
-}

-- Intrinsically scoped, with type mvars
data Term : Scope -> (tymv : TyFam) -> Type where
  Var : (n : Name) -> (n `Elem` gamma) -> Term gamma tyfam
  Lam : (n : Name) -> Ty tyfam -> Term (gamma :< n) tyfam -> Term gamma tyfam
  App : Term gamma tyfam -> Term gamma tyfam -> Term gamma tyfam
{-

{-

Context : Type
Context = SnocList (Name , Ty)


-- Intrinsically typed
data Term : Context -> Ty -> Type where
  Var : (nty : (Name,Ty))-> (pos : nty `Elem` gamma) => Term gamma (snd nty)
  Lam : (nty : (Name,Ty)) -> Term (gamma :< nty) rty -> Term gamma (Fn (snd nty) rty)
  App : Term gamma (Fn aty rty) -> Term gamma aty  -> Term gamma rty


Ex1 : Term [<]
Ex1 = Lam ("x", Tau) $ Lam ("f", Fn Tau Tau) $ App (Var ("f",Fn Tau Tau)) (Var ("x",Tau)) 
-}
{-
Ctx = List (Name, Ty)
-}
0
Ctx : Scope -> Type
Ctx gamma = ForAll gamma $ const Ty
-}
data Convertible : Ty tymv -> Ty tymv -> Type where
  TauConv : Convertible Tau Tau
  FnConv : Convertible ay ay' -> Convertible ry ry' -> Convertible (Fn ay ry) (Fn ay' ry')
  Delayed : Convertible (MV mv) ty'
  

{-
data WF : {gamma : Scope} -> Term gamma -> Ty -> Type where
  AppRule : WF fun (Fn ay' ay) -> WF arg ay -> Convertible ay' ay -> WF (App fun arg) ry

check : Ctx gamma -> (t : Term gamma) -> (ty : Ty) -> Maybe (WF t ty)  
synth : Ctx gamma -> Term gamma -> Maybe Ty


{-
mutual
  check : Ctx -> Term -> Ty -> Bool
  check g (Var n) t = case lookup n g of Nothing => False; Just t' => t == t'
  check g (Lam n t b) (Fn Tau t') = check ((n, t) :: g) b t'
  check g (App l r) t2 = case infer g r of  -- I don't like how infer doesn't call back to check, but I can't see another way to get t1
                              Nothing   => False
                              (Just t1) => check g l (Fn t1 t2)
  check _ _ _ = False
  
  infer : Ctx -> Term -> Maybe Ty
  infer g (Var n) = lookup n g
  infer g (Lam n t b) = case infer ((n, t) :: g) b of
                          (Just t') => Just $ Fn t t'
                          _         => Nothing
  infer g (App l r) = case (infer g l, infer g r) of  -- This can be split into infer l and check r
                        (Just $ Fn t1 t2, Just t3) => if t1 == t3 then Just t2 else Nothing
                        _                          => Nothing
  
-- These defs are infer-based only
wellformed : Term -> Bool
wellformed e = case infer [] e of
                 Nothing  => False
                 (Just _) => True
  
typecheck : Term -> Ty -> Bool
typecheck e t = case infer [] e of
                  Just t' => t == t'
                  Nothing => False
  
Id : Term
Id = Lam "x" Tau (Var "x")

main : IO ()
main = putStrLn "Hello from Idris2!"
