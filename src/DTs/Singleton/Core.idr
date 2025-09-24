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
data Precontext : Support -> Type
data Pretype    : Support -> Type
data Preterm    : Support -> Type

-- Variable names are carried around here
data Precontext : Support -> Type where
  Empty  : Precontext 0
  ExtVar : Precontext n -> (v : VarName) -> Pretype n -> Precontext (S n)
  ExtLet : Precontext n -> (v : VarName) -> Pretype n -> Preterm n -> Precontext (S n)

data Pretype : Support -> Type where
  Bool : Pretype n
  Singleton : Pretype n -> Preterm n -> Pretype n

data Preterm : Support -> Type where
  True  : Preterm n
  False : Preterm n
  When : Preterm n -> (v : VarName) -> Pretype (S n) -> Preterm (S n) -> Preterm (S n) -> Preterm n
  Val : Preterm n -> Preterm n
  LetVal : Preterm n -> Preterm (S n) -> Preterm n
  Var : (v : VarName) -> Fin n -> Preterm n

--- RELATIONS
{- TODO List
Relations to promote presyntax into syntax
-}

-- These stay as presyntax
data Twin : Precontext xs -> Precontext ys -> Type
data Conv : Precontext xs -> Pretype xs -> Precontext ys -> Pretype ys -> Type
data JE : Precontext xs -> Preterm xs -> Pretype xs
         -> Precontext ys -> Preterm ys -> Pretype ys
         -> Type


data Twin : Precontext xs -> Precontext ys -> Type where
  TwinEmp : Twin Empty Empty
  TwinExtVar : Twin gamma delta
               -> Conv gamma a delta b
               -> Twin (ExtVar gamma x a) (ExtVar delta y b)
  TwinExtLet : Twin gamma delta
               -> JE gamma t a delta s b
               -> Twin (ExtLet gamma x a t) (ExtLet delta y b s)

data Conv : Precontext xs -> Pretype xs -> Precontext ys -> Pretype ys -> Type where
  ConvRefl  : (a : Pretype n) -> Conv gamma a gamma a
  ConvSym   : Conv gamma a delta b
           -> Conv delta b gamma a
  ConvTrans : Conv gamma a delta b
           -> Conv delta b xi    c
           -> Conv gamma a xi    c

  ConvBoolCong : Conv gamma Bool delta Bool
  ConvSingletonCong : Conv gamma a delta b
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

  JEtrueCong  : JE gamma True  Bool delta True  Bool
  JEfalseCong : JE gamma False Bool delta False Bool

  JEwhenCong : JE gamma c Bool delta c' Bool
            -> JE (ExtLet gamma x Bool True)  t a    (ExtLet delta x' Bool True)  t' a
            -> JE (ExtLet gamma x Bool false) e a    (ExtLet delta x' Bool False) e' a
            -> JE gamma (When c x a t e) ?la delta (When c' x' a' t' e') ?ra

  JEvalCong : JE gamma t a delta s b
           -> JE gamma (Val t) (Singleton a t) delta (Val s) (Singleton b s)
