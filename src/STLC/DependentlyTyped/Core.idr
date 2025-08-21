||| Intrinsically scoped dependently typed lambda calculus.
module STLC.DependentlyTyped.Core

import Data.List
import Data.SnocList
import Data.SnocList.Elem

VarName : Type
VarName = String

Support : Type
Support = SnocList VarName

--- PRESYNTAX
data Preterm : Support -> Type where
  True  : Preterm vs
  False : Preterm vs
  ITE : Preterm vs -> Preterm vs -> Preterm vs -> Preterm vs
  Val : Preterm vs -> Preterm vs

data Pretype : Support -> Type where
  Bool : Pretype vs
  Singleton : Pretype vs -> Preterm vs -> Pretype vs

data Precontext : Support -> Type where
  Empty  : Precontext [<]
  ExtVar : Precontext vs -> (v : VarName) -> Pretype vs -> Precontext (vs :< v)
  ExtLet : Precontext vs -> (v : VarName) -> Pretype vs -> Preterm vs -> Precontext (vs :< v)

--- RELATIONS
mutual
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
