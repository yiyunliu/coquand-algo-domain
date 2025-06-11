Require Export domain_semantics.

Definition val_ok ρ0 ρ1 Γ :=
  forall i A, lookup i Γ A -> SEq A (ρ0 i) (ρ1 i).

Definition SemWt Γ a A := forall ρ0 ρ1, val_ok ρ0 ρ1 Γ -> exists d0 d1,
      compile ρ0 a d0 /\ compile ρ1 a d1 /\ SEq A d0 d1.

Lemma val_ok_ext ρ0 ρ1 Γ d0 d1 A :
  SEq A d0 d1 ->
  val_ok ρ0 ρ1 Γ ->
  val_ok (d0.:ρ0) (d1.:ρ1) (A :: Γ).
Proof.
  move => h0 h1 n B.
  inversion 1; subst.
  - done.
  - sfirstorder.
Qed.


Notation "Γ ⊨ a ∈ A" := (SemWt Γ a A) (at level 70).

Lemma ST_Var Γ i A :
  lookup i Γ A ->
  Γ ⊨ VarTm i ∈ A.
Proof.
  hauto ctrs:compile unfold:val_ok.
Qed.

Lemma ST_Fun Γ b A B :
  A :: Γ ⊨ b ∈ B ->
  Γ ⊨ Abs b ∈ Fun A B.
Proof.
  move => h ρ0 ρ1 hρ.
  do 2 eexists.
  repeat split.
  constructor. constructor.
  simpl. move => d d' hd.
  move : val_ok_ext hρ hd; repeat move/[apply].
  move => {}/h.
  hauto q:on ctrs:ap.
Qed.

Lemma ST_App Γ b a A B :
  Γ ⊨ b ∈ Fun A B ->
  Γ ⊨ a ∈ A ->
  Γ ⊨ App b a ∈ B.
Proof.
  move => h0 h1 ρ0 ρ1 hρ.
  move : h0 (hρ) => /[apply].
  move => [b0][b1][hb0][hb1]hbe.
  move : h1 (hρ) => /[apply].
  move => [a0][a1][ha0][ha1]hae.
  hauto lq:on unfold:FunSpace ctrs:compile.
Qed.
