module STLC.IntrinsicallyScoped.Examples

import Data.SnocList.Elem

import STLC.IntrinsicallyScoped.Core

Ex_base_id : Term [<]
Ex_base_id = Lam "x" Base (Var "x" Here)

Ex_check_base_id : check [<] Ex_base_id (Fn Base Base) = True
Ex_check_base_id = Refl

Ex_ill_typed : Term [<]
Ex_ill_typed = Lam "x" (Fn Base Base) (Var "x" Here)

failing
  Ex_ill_scoped1 : Term [<] Unit
  Ex_ill_scoped1 = Lam "x" Base (Var "y" Here)

  Ex_ill_scoped2 : Term [<] Unit
  Ex_ill_scoped2 = Lam "x" Base (Var "x" (There Here))
