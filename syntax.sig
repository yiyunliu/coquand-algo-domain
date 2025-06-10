Tm(VarTm) : Type
Ty : Type

Void : Ty
Fun : Ty -> Ty -> Ty

Abs : (bind Tm in Tm) -> Tm
App : Tm -> Tm -> Tm
