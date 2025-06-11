Require Export domain_semantics typing.

Theorem fundamental Γ a A :
  Γ ⊢ a ∈ A -> Γ ⊨ a ∈ A.
Proof. induction 1; eauto using ST_App, ST_Var, ST_Fun. Qed.
