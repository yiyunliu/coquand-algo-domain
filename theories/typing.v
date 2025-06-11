Require Export imports.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70).
Reserved Notation "Γ ⊢ a ≡ b ∈ A" (at level 70).
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

Inductive Eq Γ : Tm -> Tm -> Ty -> Prop :=
| J_Refl a A :
  Γ ⊢ a ∈ A ->
  Γ ⊢ a ≡ a ∈ A
| J_Sym a b A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ a ∈ A
| J_Trans a b c A :
  Γ ⊢ a ≡ b ∈ A ->
  Γ ⊢ b ≡ c ∈ A ->
  Γ ⊢ a ≡ c ∈ A
| J_App b0 b1 a0 a1 A B :
  Γ ⊢ b0 ≡ b1 ∈ Fun A B ->
  Γ ⊢ a0 ≡ a1 ∈ A ->
  Γ ⊢ App b0 a0 ≡ App b1 a1 ∈ B
| J_β b a A B :
  A :: Γ ⊢ b ∈ B ->
  Γ ⊢ a ∈ A ->
  Γ ⊢ App (Abs b) a ≡ b[a..] ∈ B
| J_η a b A B :
  A :: Γ ⊢ App a⟨shift⟩ (VarTm var_zero) ≡
    App b⟨shift⟩ (VarTm var_zero) ∈ B ->
  Γ ⊢ a ≡ b ∈ Fun A B
where "Γ ⊢ a ≡ b ∈ A" := (Eq Γ a b A).
