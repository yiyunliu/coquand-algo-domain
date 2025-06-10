Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Tm : Type :=
  | VarTm : nat -> Tm
  | Abs : Tm -> Tm
  | App : Tm -> Tm -> Tm.

Lemma congr_Abs {s0 : Tm} {t0 : Tm} (H0 : s0 = t0) : Abs s0 = Abs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Abs x) H0)).
Qed.

Lemma congr_App {s0 : Tm} {s1 : Tm} {t0 : Tm} {t1 : Tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : App s0 s1 = App t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => App x s1) H0))
         (ap (fun x => App t0 x) H1)).
Qed.

Lemma upRen_Tm_Tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_Tm (xi_Tm : nat -> nat) (s : Tm) {struct s} : Tm :=
  match s with
  | VarTm s0 => VarTm (xi_Tm s0)
  | Abs s0 => Abs (ren_Tm (upRen_Tm_Tm xi_Tm) s0)
  | App s0 s1 => App (ren_Tm xi_Tm s0) (ren_Tm xi_Tm s1)
  end.

Lemma up_Tm_Tm (sigma : nat -> Tm) : nat -> Tm.
Proof.
exact (scons (VarTm var_zero) (funcomp (ren_Tm shift) sigma)).
Defined.

Fixpoint subst_Tm (sigma_Tm : nat -> Tm) (s : Tm) {struct s} : Tm :=
  match s with
  | VarTm s0 => sigma_Tm s0
  | Abs s0 => Abs (subst_Tm (up_Tm_Tm sigma_Tm) s0)
  | App s0 s1 => App (subst_Tm sigma_Tm s0) (subst_Tm sigma_Tm s1)
  end.

Lemma upId_Tm_Tm (sigma : nat -> Tm) (Eq : forall x, sigma x = VarTm x) :
  forall x, up_Tm_Tm sigma x = VarTm x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_Tm (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = VarTm x) (s : Tm) {struct s} :
subst_Tm sigma_Tm s = s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | Abs s0 =>
      congr_Abs (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (idSubst_Tm sigma_Tm Eq_Tm s0) (idSubst_Tm sigma_Tm Eq_Tm s1)
  end.

Lemma upExtRen_Tm_Tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Tm_Tm xi x = upRen_Tm_Tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : Tm) {struct s} :
ren_Tm xi_Tm s = ren_Tm zeta_Tm s :=
  match s with
  | VarTm s0 => ap (VarTm) (Eq_Tm s0)
  | Abs s0 =>
      congr_Abs
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  end.

Lemma upExt_Tm_Tm (sigma : nat -> Tm) (tau : nat -> Tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Tm_Tm sigma x = up_Tm_Tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : Tm) {struct s} :
subst_Tm sigma_Tm s = subst_Tm tau_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | Abs s0 =>
      congr_Abs
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s0)
  | App s0 s1 =>
      congr_App (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  end.

Lemma up_ren_ren_Tm_Tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Tm_Tm zeta) (upRen_Tm_Tm xi) x = upRen_Tm_Tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(rho_Tm : nat -> nat) (Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x)
(s : Tm) {struct s} : ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm rho_Tm s :=
  match s with
  | VarTm s0 => ap (VarTm) (Eq_Tm s0)
  | Abs s0 =>
      congr_Abs
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  end.

Lemma up_ren_subst_Tm_Tm (xi : nat -> nat) (tau : nat -> Tm)
  (theta : nat -> Tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Tm_Tm tau) (upRen_Tm_Tm xi) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_Tm (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Tm) {struct s} :
subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | Abs s0 =>
      congr_Abs
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  end.

Lemma up_subst_ren_Tm_Tm (sigma : nat -> Tm) (zeta_Tm : nat -> nat)
  (theta : nat -> Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_Tm_Tm zeta_Tm)) (up_Tm_Tm sigma) x =
  up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_Tm shift (upRen_Tm_Tm zeta_Tm)
                (funcomp shift zeta_Tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_Tm zeta_Tm shift (funcomp shift zeta_Tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_Tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_Tm (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x) 
(s : Tm) {struct s} :
ren_Tm zeta_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | Abs s0 =>
      congr_Abs
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  end.

Lemma up_subst_subst_Tm_Tm (sigma : nat -> Tm) (tau_Tm : nat -> Tm)
  (theta : nat -> Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_Tm_Tm tau_Tm)) (up_Tm_Tm sigma) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_Tm shift (up_Tm_Tm tau_Tm)
                (funcomp (up_Tm_Tm tau_Tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_Tm tau_Tm shift
                      (funcomp (ren_Tm shift) tau_Tm) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_Tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Tm) {struct s} :
subst_Tm tau_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | Abs s0 =>
      congr_Abs
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  end.

Lemma renRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) (s : Tm) :
  ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Tm_pointwise (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (ren_Tm xi_Tm))
    (ren_Tm (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) (s : Tm) :
  subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm_pointwise (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (ren_Tm xi_Tm))
    (subst_Tm (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) (s : Tm) :
  ren_Tm zeta_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm_pointwise (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) (s : Tm) :
  subst_Tm tau_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm_pointwise (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Tm_Tm (xi : nat -> nat) (sigma : nat -> Tm)
  (Eq : forall x, funcomp (VarTm) xi x = sigma x) :
  forall x, funcomp (VarTm) (upRen_Tm_Tm xi) x = up_Tm_Tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_Tm (xi_Tm : nat -> nat) (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (VarTm) xi_Tm x = sigma_Tm x) (s : Tm) {struct s}
   : ren_Tm xi_Tm s = subst_Tm sigma_Tm s :=
  match s with
  | VarTm s0 => Eq_Tm s0
  | Abs s0 =>
      congr_Abs
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s0)
  | App s0 s1 =>
      congr_App (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  end.

Lemma rinstInst'_Tm (xi_Tm : nat -> nat) (s : Tm) :
  ren_Tm xi_Tm s = subst_Tm (funcomp (VarTm) xi_Tm) s.
Proof.
exact (rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (ren_Tm xi_Tm) (subst_Tm (funcomp (VarTm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm (s : Tm) : subst_Tm (VarTm) s = s.
Proof.
exact (idSubst_Tm (VarTm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm_pointwise : pointwise_relation _ eq (subst_Tm (VarTm)) id.
Proof.
exact (fun s => idSubst_Tm (VarTm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Tm (s : Tm) : ren_Tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Tm_pointwise : pointwise_relation _ eq (@ren_Tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma varL'_Tm (sigma_Tm : nat -> Tm) (x : nat) :
  subst_Tm sigma_Tm (VarTm x) = sigma_Tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Tm_pointwise (sigma_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm sigma_Tm) (VarTm)) sigma_Tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Tm (xi_Tm : nat -> nat) (x : nat) :
  ren_Tm xi_Tm (VarTm x) = VarTm (xi_Tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Tm_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm xi_Tm) (VarTm))
    (funcomp (VarTm) xi_Tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive Ty : Type :=
  | Void : Ty
  | Fun : Ty -> Ty -> Ty.

Lemma congr_Void : Void = Void.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Fun {s0 : Ty} {s1 : Ty} {t0 : Ty} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : Fun s0 s1 = Fun t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Fun x s1) H0))
         (ap (fun x => Fun t0 x) H1)).
Qed.

Class Up_Tm X Y :=
    up_Tm : X -> Y.

#[global] Instance Subst_Tm : (Subst1 _ _ _) := @subst_Tm.

#[global] Instance Up_Tm_Tm : (Up_Tm _ _) := @up_Tm_Tm.

#[global] Instance Ren_Tm : (Ren1 _ _ _) := @ren_Tm.

#[global]
Instance VarInstance_Tm : (Var _ _) := @VarTm.

Notation "[ sigma_Tm ]" := (subst_Tm sigma_Tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_Tm ]" := (subst_Tm sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm (only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm_Tm (only printing)  : subst_scope.

Notation "⟨ xi_Tm ⟩" := (ren_Tm xi_Tm)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Tm xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := VarTm ( at level 1, only printing)  : subst_scope.

Notation "x '__Tm'" := (@ids _ _ VarInstance_Tm x)
( at level 5, format "x __Tm", only printing)  : subst_scope.

Notation "x '__Tm'" := (VarTm x) ( at level 5, format "x __Tm")  :
subst_scope.

#[global]
Instance subst_Tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Tm f_Tm s = subst_Tm g_Tm t')
         (ext_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Tm f_Tm s = ren_Tm g_Tm t')
         (extRen_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Tm f_Tm g_Tm Eq_Tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1,
                      Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Tm, Var, ids,
                                            Ren_Tm, Ren1, ren1, Up_Tm_Tm,
                                            Up_Tm, up_Tm, Subst_Tm, Subst1,
                                            subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Tm_pointwise
                 | progress setoid_rewrite substSubst_Tm
                 | progress setoid_rewrite substRen_Tm_pointwise
                 | progress setoid_rewrite substRen_Tm
                 | progress setoid_rewrite renSubst_Tm_pointwise
                 | progress setoid_rewrite renSubst_Tm
                 | progress setoid_rewrite renRen'_Tm_pointwise
                 | progress setoid_rewrite renRen_Tm
                 | progress setoid_rewrite varLRen'_Tm_pointwise
                 | progress setoid_rewrite varLRen'_Tm
                 | progress setoid_rewrite varL'_Tm_pointwise
                 | progress setoid_rewrite varL'_Tm
                 | progress setoid_rewrite rinstId'_Tm_pointwise
                 | progress setoid_rewrite rinstId'_Tm
                 | progress setoid_rewrite instId'_Tm_pointwise
                 | progress setoid_rewrite instId'_Tm
                 | progress unfold up_Tm_Tm, upRen_Tm_Tm, up_ren
                 | progress cbn[subst_Tm ren_Tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1,
                  Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Tm_pointwise;
                  try setoid_rewrite rinstInst'_Tm.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_Tm_pointwise;
                  try setoid_rewrite_left rinstInst'_Tm.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_Tm: rewrite.

#[global] Hint Opaque ren_Tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

