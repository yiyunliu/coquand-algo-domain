Require Export imports.

(* Applicative structures *)
Inductive D_ne : Type :=
| D_Idx (i : nat)
| D_App (f : D_ne) (a : D)
with D : Type :=
| D_Fun (body : Tm) (ρ : nat -> D)
| D_Neu (d : D_ne).
