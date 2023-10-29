Require Import Utf8.
Require Import IxFree.Lib.
Require Import List.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Binding.Env.

Require Import FOmegaEq.Unary.Realize FOmegaEq.Types FOmegaEq.Syntax FOmegaEq.OpSemantics FOmegaEq.Interp FOmegaEq.Universe FOmegaEq.Unary.Compat.
Require Import FOmegaEq.Presheaves.
Require Import FOmegaEq.Typing.
Require FOmegaEq.Kinds.
Import -(notations) Kinds.
Import Kinds.DED_kind.
Require Import Morphisms.

Lemma adequacy_now_preserve {P : value ∅ -> Prop}
  (e : expr ∅)
  : 0 ⊨ ECL (fun v => (P v)ᵢ) e -> (∃ v, e = e_val v ∧ P v) ∨ (∃ e', head_step e e').
Proof.
  intros H.
  apply (I_fix_unroll _ _ (ECC_contr _)) in H.
  idestruct H as H H.
  - idestruct H as v H; idestruct H as EQ HHH.
    subst; left; eexists _; split; [reflexivity | assumption].
  - idestruct H as v H; idestruct H as HS HHH; clear HHH.
    right; eexists _; eassumption.
Qed.

Lemma adequacy_now {P}
  (e : expr ∅)
  : 0 ⊨ ECL P e -> (∃ v, e = e_val v) ∨ (∃ e', head_step e e').
Proof.
  intros H.
  apply (I_fix_unroll _ _ (ECC_contr _)) in H.
  idestruct H as H H.
  - idestruct H as v H; idestruct H as EQ HHH.
    subst; left; eexists _; reflexivity.
  - idestruct H as v H; idestruct H as HS HHH; clear HHH.
    right; eexists _; eassumption.
Qed.

Lemma adequacy_head_step {n P}
  (e : expr ∅)
  : S n ⊨ ECL P e -> ∀ e', head_step e e' -> n ⊨ ECL P e'.
Proof.
  intros HE e' HS.
  apply (I_fix_unroll _ _ (ECC_contr _)) in HE.
  idestruct HE as HE HE.
  - idestruct HE as v HE; idestruct HE as EQ HHH; clear HHH.
    subst; exfalso; eapply val_head_step; eassumption.
  - idestruct HE as e'' HE; idestruct HE as HS' HE.
    rewrite I_later_shift in HE.
    rewrite (@head_step_det e e' e''); assumption.
Qed.

Lemma adequacy_nstep {n m P}
  (e : expr ∅)
  : m + n ⊨ ECL P e -> ∀ e', nsteps m e e' -> n ⊨ ECL P e'.
Proof.
  intros HE e' HS.
  induction HS as [| ? ? ? ? ? ? IH].
  - apply HE.
  - rewrite plus_Sn_m in HE.
    apply IH.
    eapply adequacy_head_step; eassumption.
Qed.

Lemma adequacy
  (e : expr ∅) (τ : typ KTyp ε)
  : logrelE mtC nil Env.empty_env e τ -> safe e.
Proof.
  intros HE e' HS.
  rewrite erased_steps_nsteps in HS.
  destruct HS as [n HS].
  eapply adequacy_now.
  eapply adequacy_nstep; [rewrite <-plus_n_O | eassumption].
  assert (Hη : @sub_relS ε ε ε η_id η_id η_id).
  { intros []. }
  assert (HΨ : ∀ ψ : constr ε, In ψ nil → ctrue (〚 ψ 〛ᶜ η_id)).
  { intros ? []. }
  specialize (HE η_id Hη HΨ ı%bind n).
  rewrite ebind_id in HE; [| intros []].
  apply HE.
  iintro x; destruct x.
Qed.

Lemma semantical_soundness
  (e : expr ∅) (τ : typ KTyp ε)
  : mtC ∣ nil ∣ Env.empty_env ⊢ₑ e : τ -> safe e.
Proof.
  intros H; eapply adequacy, fl_expr, H.
Qed.
