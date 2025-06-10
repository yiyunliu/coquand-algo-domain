Require Export List.
Inductive lookup {A} : nat -> list A -> A -> Prop :=
| here a Γ : lookup 0 (a :: Γ) a
| there n Γ a b : lookup n Γ a -> lookup (S n) (b :: Γ) a.

Hint Constructors lookup : lookup.

Lemma lookup_deterministic (T :Type) n Γ (A : T) B :
  lookup n Γ A ->
  lookup n Γ B ->
  A = B.
Proof.
  induction 1; inversion 1; subst; eauto with lookup.
Qed.
