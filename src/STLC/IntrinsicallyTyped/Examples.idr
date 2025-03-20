module STLC.IntrinsicallyTyped.Examples

import Data.SnocList.Elem

import STLC.IntrinsicallyTyped.Core

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
