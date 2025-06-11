Require Import domain.

Inductive compile : (nat -> D) -> Tm -> D -> Prop :=
| C_Var ρ i :
  compile ρ (VarTm i) (ρ i)
| C_Abs ρ a :
  compile ρ (Abs a) (D_Fun a ρ)
| C_App ρ a d b d' d'' :
  compile ρ a d ->
  compile ρ b d' ->
  ap d d' d'' ->
  compile ρ (App a b) d''
with ap : D -> D -> D -> Prop :=
| A_Fun a ρ (d d' d'' : D) :
  compile (d .: ρ) a d' ->
  ap (D_Fun a ρ) d d'
| A_Neu e d :
  ap (D_Neu e) d (D_Neu (D_App e d)).

Inductive D_eq (n : nat) : D -> D -> Prop :=
| E_Neu e0 e1 :
  D_ne_eq n e0 e1 ->
  D_eq n (D_Neu e0) (D_Neu e1)

| E_FunNeu a ρ e d :
  compile (D_Neu (D_Idx n) .: ρ) a d ->
  D_eq (S n) d (D_Neu (D_App e (D_Neu (D_Idx n)))) ->
  D_eq n (D_Fun a ρ) (D_Neu e)

| E_FunFun a ρ d a' ρ' d' :
  compile (D_Neu (D_Idx n) .: ρ) a d ->
  compile (D_Neu (D_Idx n) .: ρ') a' d' ->
  D_eq (S n) d d' ->
  D_eq n (D_Fun a ρ) (D_Fun a' ρ')

| E_NeuFun a ρ e d :
  compile (D_Neu (D_Idx n) .: ρ) a d ->
  D_eq (S n) (D_Neu (D_App e (D_Neu (D_Idx n)))) d ->
  D_eq n (D_Neu e) (D_Fun a ρ)

with D_ne_eq (n : nat) : D_ne -> D_ne -> Prop :=
| E_Idx i :
  D_ne_eq n (D_Idx i) (D_Idx i)
| E_App e0 e1 d0 d1 :
  D_ne_eq n e0 e1 ->
  D_eq n d0 d1 ->
  D_ne_eq n (D_App e0 d0) (D_App e1 d1).

Definition S_Ne (d0 d1 : D) :=
  match d0, d1 with
  | D_Neu d0, D_Neu d1 => forall n, D_ne_eq n d0 d1
  | _, _ => False
  end.

Definition FunSpace (E_Dom E_CoDom : D -> D -> Prop) (d0 d1 : D) :=
  forall e0 e1, E_Dom e0 e1 -> exists d0' d1', ap d0 e0 d0' /\ ap d1 e1 d1' /\ E_CoDom d0' d1'.

Fixpoint SEq (A : Ty) : D -> D -> Prop :=
  match A with
  | Void => S_Ne
  | Fun A B => FunSpace (SEq A) (SEq B)
  end.

Lemma adequacy  : forall A,
    (forall n d0 d1, SEq A d0 d1 -> D_eq n d0 d1) /\
      (forall e0 e1, (forall n, D_ne_eq n e0 e1) -> SEq A (D_Neu e0) (D_Neu e1)).
Proof.
  elim => //=.
  - hauto lq:on unfold:S_Ne inv:D ctrs:D_eq.
  - move => A [ihA0 ihA1] B [ihB0 ihB1].
    split.
    + move => n d0 d1.
      rewrite /FunSpace => hFun.
      have : SEq A (D_Neu (D_Idx n)) (D_Neu (D_Idx n)) by qauto ctrs:D_ne_eq.
      move /hFun.
      move => [d0'][d1'][h0][h1].
      move => {}/ihB0 => ihB0.
      move {ihA0 ihA1 ihB1}.
      destruct d0, d1.
      hauto q:on ctrs:D_eq inv:ap.
      hauto q:on ctrs:D_eq inv:ap.
      hauto q:on ctrs:D_eq inv:ap.
      hauto lq:on rew:off ctrs:D_ne_eq, D_eq inv:D_ne_eq, D_eq,ap.
    + rewrite /FunSpace.
      move => e0 e1 he e2 e3 hDom.
      do 2 eexists.
      repeat split. constructor. constructor.
      apply ihB1.
      move => n.
      move : he => /(_ n). move /(ihA0 n) : hDom.
      clear. move => h0 h1. by constructor.
Qed.
