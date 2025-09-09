||| Intrinsically scoped dependently typed lambda calculus.
module DTs.Singleton.Core

import Data.List
import Data.SnocList
import Data.SnocList.Elem
import Data.Fin

VarName : Type
VarName = String

Support : Type
Support = Nat

--- PRESYNTAX
data Preterm : Support -> Type where
  True  : Preterm n
  False : Preterm n
  ITE : Preterm n -> Preterm n -> Preterm n -> Preterm n
  Val : Preterm n -> Preterm n
  LetVal : Preterm n -> Preterm (S n) -> Preterm n
  Var : (v : VarName) -> Fin n -> Preterm n

data Pretype : Support -> Type where
  Bool : Pretype n
  Singleton : Pretype n -> Preterm n -> Pretype n

-- Variable names are carried around here
data Precontext : Support -> Type where
  Empty  : Precontext 0
  ExtVar : Precontext n -> (v : VarName) -> Pretype n -> Precontext (S n)
  ExtLet : Precontext n -> (v : VarName) -> Pretype n -> Preterm n -> Precontext (S n)

--- RELATIONS
{- TODO
Relations to promote presyntax into syntax
-}

-- These stay as presyntax
data TwinCtx : Precontext xs -> Precontext ys -> Type
data Conv : Precontext xs -> Pretype xs -> Precontext ys -> Pretype ys -> Type
data JE : Precontext xs -> Preterm xs -> Pretype xs
         -> Precontext ys -> Preterm ys -> Pretype ys
         -> Type


data TwinCtx : Precontext xs -> Precontext ys -> Type where
  TwinCtxEmp : TwinCtx Empty Empty
  TwinCtxExtVar : TwinCtx gamma delta
               -> Conv gamma a delta b
               -> TwinCtx (ExtVar gamma x a) (ExtVar delta y b)
  TwinCtxExtLet : TwinCtx gamma delta
               -> JE gamma t a delta s b
               -> TwinCtx (ExtLet gamma x a t) (ExtLet delta y b s)

data Conv : Precontext xs -> Pretype xs -> Precontext ys -> Pretype ys -> Type where
  ConvBool : Conv gamma Bool gamma Bool
  ConvSingleton : Conv gamma a delta b
               -> JE gamma t a delta s b
               -> Conv gamma (Singleton a t) delta (Singleton b s)

data JE : Precontext xs -> Preterm xs -> Pretype xs
       -> Precontext ys -> Preterm ys -> Pretype ys
       -> Type where
  JERefl : (gamma : Precontext vs) -> (t : Preterm vs) -> (a : Pretype vs)
        -> JE gamma t a gamma t a
  JESym : JE gamma t  a delta s b
       -> JE delta s b gamma t a
  JETrans : JE gamma t a delta s b
         -> JE delta s b xi    r c
         -> JE gamma t a xi    r c
