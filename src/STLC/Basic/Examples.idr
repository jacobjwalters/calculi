module STLC.Basic.Examples

import STLC.Basic.Core

Ex_base_id : Term
Ex_base_id = Lam "x" Base (EVar "x")

Ex_check_base_id : check [<] Ex_base_id (Fn Base Base) = True
Ex_check_base_id = Refl

Ex_ill_scoped1 : Term
Ex_ill_scoped1 = Lam "x" Base (EVar "y")

Ex_ill_scoped2 : Term
Ex_ill_scoped2 = Lam "x" Base (EVar "x")

Ex_ill_typed : Term
Ex_ill_typed = Lam "x" (Fn Base Base) (EVar "x")
