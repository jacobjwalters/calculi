module STLC.TypeLevelMetavars.Examples

import Data.SnocList.Elem

import STLC.TypeLevelMetavars.Core

Ex_base_id : Term [<] Unit
Ex_base_id = Lam "x" Base (Var "x" Here)

Ex_check_base_id : check [<] Ex_base_id (Fn Base Base) = True
Ex_check_base_id = Refl

Ex_mv_str_id : Term [<] String
Ex_mv_str_id = Lam "x" (MV "idty") (Var "x" Here)

Ex_check_mv_str_id : check [<] Ex_mv_str_id (Fn Base Base) = True
Ex_check_mv_str_id = Refl

Ex_ill_typed : Term [<] Unit
Ex_ill_typed = Lam "x" (Fn Base Base) (Var "x" Here)

failing
  Ex_ill_scoped1 : Term [<] Unit
  Ex_ill_scoped1 = Lam "x" Base (Var "y" Here)

  Ex_ill_scoped2 : Term [<] Unit
  Ex_ill_scoped2 = Lam "x" Base (Var "x" (There Here))
