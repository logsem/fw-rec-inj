Require Import Lang.FOmegaEq.Syntax.
Require Import Utf8.
Require Import Binding.Lib.
Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties Coq.Classes.RelationClasses.

Reserved Notation "e ↦ e'" (at level 70).

(* The reduction relation (Fig. 6) *)
Inductive head_step : expr ∅ → expr ∅ → Prop :=
| LamBetaRec e v : (rec e) v ↦ subst (Inc := inc) ((subst (Inc := inc) e) (shift v)) (rec e)
| LamBetaE e v : (ƛ e) v ↦ subst (Inc := inc) e v
| LamBetaT e : e_tapp (Λ e) ↦ e
| LamBetaC e : e_capp (ƛᶜ e) ↦ e
| ProjLE v1 v2 : e_proj L ⟨v1, v2⟩ ↦ v1
| ProjRE v1 v2 : e_proj R ⟨v1, v2⟩ ↦ v2
| CaseLE v e1 e2 : e_case (v_inj L v) e1 e2 ↦ subst (Inc := inc) e1 v
| CaseRE v e1 e2 : e_case (v_inj R v) e1 e2 ↦ subst (Inc := inc) e2 v
| UnpackE v e : e_unpack (v_pack v) e ↦ subst (Inc := inc) e v
| UnrollE v : e_unroll (v_roll v) ↦ v
| WithE v e : e_lwith ⟨v⟩ᶜ e ↦ subst (Inc := inc) e v
| BindE e' (v : value ∅) : v >>= e' ↦ subst (Inc := inc) e' v
| BindE' e e' e'' : e' ↦ e'' -> e_bind e' e ↦ e_bind e'' e
where "e ↦ e'" := (head_step e%syn e'%syn).

Definition step := clos_refl_trans_1n (expr ∅) head_step.

Notation "e ↦* e'" := (step e%syn e'%syn) (at level 70).

(* The analogue of Definition 4.5, slightly nicer constructively *)
Definition safe (e : expr ∅) :=
  forall e', e ↦* e' -> (∃ v, e' = e_val v) \/ (exists e'', e' ↦ e'').

Lemma val_head_step (v : value ∅) (e : expr ∅) (red : v ↦ e)
  : False.
Proof.
  inversion red.
Qed.

Lemma head_step_det {e e' e'' : expr ∅} : e ↦ e' -> e ↦ e'' -> e' = e''.
Proof.
  intros H.
  revert e''.
  induction H; intros t G;
    try (inversion G; subst; reflexivity; fail).
  - inversion G; subst.
    + reflexivity.
    + apply val_head_step in H2; contradiction.
  - inversion G; subst.
    + apply val_head_step in H; contradiction.
    + f_equal.
      now apply IHhead_step.
Qed.

Lemma ectx_step {e e' : expr ∅} {K} : e ↦* e' -> e >>= K ↦* e' >>= K.
Proof.
  intros H.
  revert K.
  induction H as [| ? ? ? ? ? IH].
  - intros K; now apply rt1n_refl.
  - intros K.
    eapply Relation_Operators.rt1n_trans.
    2: apply IH.
    now apply BindE'.
Qed.

Lemma head_step_step {e e' : expr ∅} : e ↦ e' -> e ↦* e'.
Proof.
  econstructor; [eassumption |].
  constructor.
Qed.

Lemma step_arg {e e'} {v : value ∅}
  : e' ↦* v -> e' >>= e ↦* subst e v.
Proof.
  intros H.
  revert e.
  remember (e_val v) as R.
  induction H as [| ? ? ? ? ? IH]; subst.
  - intros e.
    apply head_step_step.
    constructor.
  - intros e.
    specialize (IH eq_refl e).
    apply clos_rt_rt1n.
    eapply rt_trans.
    + apply clos_rt_rt1n_iff.
      apply clos_rt1n_step.
      constructor; eassumption.
    + apply clos_rt_rt1n_iff.
      apply IH.
Qed.

Lemma step_val {e} {v : value ∅}
  : v ↦* e -> e = v.
Proof.
  remember (e_val v) as e₃ eqn:HEQ.
  intros H.
  induction H; subst.
  - reflexivity.
  - exfalso; eapply val_head_step; eassumption.
Qed.

Lemma step_det' {e₁ e₂} {v : value ∅}
  : e₁ ↦ e₂ -> e₁ ↦* v -> e₂ = v \/ e₂ ↦* v.
Proof.
  remember (e_val v) as e₃ eqn:HEQ.
  intros H G.
  revert e₂ H.
  induction G; intros e₂ J.
  - subst; exfalso; eapply val_head_step; eassumption.
  - eapply head_step_det in J; [| apply H].
    subst; right; apply G.
Qed.

Lemma step_det {e₁ e₂} {v : value ∅}
  : e₁ ↦* e₂ -> e₁ ↦* v -> e₂ = v \/ e₂ ↦* v.
Proof.
  intros H.
  revert v.
  induction H as [| ? ? ? ? ? IH].
  - intros v G.
    right; apply G.
  - intros v G.
    destruct (step_det' H G).
    + subst; apply IH; constructor.
    + apply IH; assumption.
Qed.

Inductive nsteps : nat -> expr ∅ -> expr ∅ -> Prop :=
| nsteps_step ρ :
  nsteps 0 ρ ρ
| nsteps_l n ρ1 ρ2 ρ3 :
  head_step ρ1 ρ2 ->
  nsteps n ρ2 ρ3 →
  nsteps (S n) ρ1 ρ3.
Local Hint Constructors nsteps : core.

Lemma erased_steps_nsteps (ρ1 ρ2 : expr ∅) :
  step ρ1 ρ2 ↔ ∃ n, nsteps n ρ1 ρ2.
Proof.
  split.
  - induction 1; firstorder eauto.
  - intros (n & Hsteps).
    induction Hsteps.
    + now constructor.
    + eapply Relation_Operators.rt1n_trans; eauto.
Qed.
