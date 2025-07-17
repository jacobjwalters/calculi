module STLC.Basic.Syntax

import STLC.Basic.Core

import Language.Reflection

%language ElabReflection

export
stlcType : TTImp -> Elab TTImp
stlcType b@(IVar fc (UN (Basic "Base"))) = pure b
stlcType (IPi _ MW ExplicitArg Nothing a r) = do
  a <- stlcType a
  r <- stlcType r
  pure `(Fn ~a ~r)
stlcType h@(IHole    _ _) = pure h
stlcType i@(Implicit _ _) = pure i
stlcType t = failAt (getFC t) "Expected STLC type constructor (Base or a -> b)"

export
term : TTImp -> Elab TTImp
term (IVar fc (UN (Basic nm))) = do
  let nm = IPrimVal fc $ Str nm
  pure $ `(EVar ~nm)
term (ILam fc MW ExplicitArg (Just (UN (Basic nm))) t body) = do
  let nm = IPrimVal fc $ Str nm
  t <- stlcType t
  body <- term body
  pure $ mapTopmostFC (const fc) `(Lam ~nm ~t ~body)
term (ILet fc lhsFC MW nm t val body) = do
  assert_total $ term (IApp lhsFC (ILam lhsFC MW ExplicitArg (Just nm) t body) val)
term (IApp fc f x) = do
  f <- term f
  x <- term x
  pure $ mapTopmostFC (const fc) `(App ~f ~x)
term h@(IHole _ _) = pure h
term t = failAt (getFC t) "Unsupported syntactical construct. Expected variable, lambda, let, or application."

export
fromTTImp : TTImp -> Elab Term
fromTTImp t = check !(term t)

Id : Term
Id = %runElab `(\x : Base => x)

failing "reflection: Expected STLC type constructor"
  wrongId : Term
  wrongId = %runElab `(\x : Int => x)

t1 : Term
t1 = %runElab `(let x : Base -> Base = y in (\w : Base => v) z)
