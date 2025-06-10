Require Export imports.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).

Inductive Wt Γ : Tm -> Ty -> Prop :=
| T_Var i A :
  lookup i Γ A ->
  Γ ⊢ VarTm i ∈ A
| T_App b a A B :
  Γ ⊢ b ∈ Fun A B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ App b a ∈ B
| T_Abs b A B :
  A::Γ ⊢ b ∈ B ->
  Γ ⊢ Abs b ∈ Fun A B
where "Γ ⊢ a ∈ A" := (Wt Γ a A).
