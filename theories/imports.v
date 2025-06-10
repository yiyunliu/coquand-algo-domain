Require Export ssreflect Autosubst2.syntax Autosubst2.core Autosubst2.unscoped listutils.
From Hammer Require Export Tactics.
Notation "s '..'" := (scons s ids) (at level 1, format "s ..") : subst_scope.


Notation "s [ sigmatm ]" := (subst_Tm sigmatm s) (at level 7, left associativity) : subst_scope.
Notation "s ⟨ xitm ⟩" := (ren_Tm xitm s) (at level 7, left associativity) : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50) : subst_scope.

Global Open Scope subst_scope.
