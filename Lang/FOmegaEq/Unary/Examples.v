Require Import Utf8.
Require FOmegaEq.Kinds.
Require Import FOmegaEq.Types FOmegaEq.Syntax FOmegaEq.Universe FOmegaEq.Interp FOmegaEq.Unary.Realize FOmegaEq.Unary.Compat.
Require Import IxFree.Lib.
Require Import Binding.Intrinsic Binding.Lib Binding.Set.
Require Import FOmegaEq.OpSemantics.

Notation "∅" := Empty_set.

Section test1.

  Definition ty0 : typ (Kinds.KArr Kinds.KTyp Kinds.KTyp) ε := (t_lam (t_app (t_app (t_ctor Kinds.tc_arr) (t_var Kinds.KTyp (VZ : dom (_ ▹ _)) eq_refl)) (t_var Kinds.KTyp (VZ : dom (_ ▹ _)) eq_refl))).
  Definition ty1 : typ Kinds.KTyp ε := (t_app (t_ctor (Kinds.tc_all Kinds.KTyp)) ty0).

  Definition val1 : value ∅ := (v_tlam (e_val (v_lam (e_val (v_var VZ))))).

  Lemma valty1 : Typing.typing_val ε nil ε val1 ty1.
  Proof.
    repeat constructor.
  Qed.

  Lemma valtysem1 : logrelV ε nil ε val1 ty1.
  Proof.
    apply fl_val, valty1.
  Qed.

  Definition expr1 (v : value ∅) : expr ∅ :=
    e_bind (e_tapp val1)
      (e_app (v_var VZ) (Core.shift v)).

  Lemma test1_prf (v : value ∅) (P : IRel (value ∅ →ₛ *ₛ)%irel_sig)
    : ∀ n, n ⊨ P v -> n ⊨ ECL P (expr1 v).
  Proof.
    intros n.
    unfold expr1, val1.
    unshelve epose proof (valtysem1 η_id _ _ ı%bind n _) as H.
    { intros []. }
    { intros ? []. }
    { iintro x; destruct x. }
    term_simpl in H.
    intros HV.
    unfold reflect in H; simpl in H.
    unfold viewG, view in H.
    simpl in H.
    unfold eq_rect_r in H.
    simpl in H.
    apply (I_fix_unroll _ _ RPR_contr) in H.
    simpl in H.
    idestruct_exists H x H'.
    idestruct_conj H' H₁ H₂.
    apply I_Prop_elim in H₁.
    inversion H₁; subst.
    ispecialize H₂ (@neu_rel ε P).
    unfold Presheaves.eq1 in H₂.
    unfold interpNeu in H₂.
    simpl in H₂.
    ispecialize_arrow H₂; [reflexivity |].
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    iexists (e_bind
               (e_val (v_lam (e_val (v_var VZ))))
               (e_app (v_var VZ) (Core.shift v))).
    isplit; [apply BindE'; constructor |].
    later_shift.
    unfold interpNeu; term_simpl; foldArrs.
    unfold viewG, view; simpl.
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    iexists (subst (e_app (v_var VZ) (Core.shift v)) (v_lam (e_val (v_var VZ)))).
    isplit; [constructor |].
    later_shift.
    term_simpl.
    apply (I_fix_unroll _ _ (ECC_contr _)) in H₂.
    simpl in H₂.
    idestruct H₂ as G1 G2.
    - idestruct_exists G1 x' H'.
      idestruct_conj H' H₁' H₂.
      apply I_Prop_elim in H₁'.
      inversion H₁'; subst.
      apply (I_fix_unroll _ _ RPR_contr) in H₂.
      simpl in H₂.
      ispecialize H₂ v.
      ispecialize_arrow H₂; [assumption |].
      apply (I_fix_roll _ _ (ECC_contr _)).
      unfold ECL in H₂.
      apply (I_fix_unroll _ _ (ECC_contr _)) in H₂.
      apply H₂.
    - idestruct_exists G2 x' H'.
      idestruct_conj H' H₁' H₂.
      apply I_Prop_elim in H₁'.
      apply val_head_step in H₁'.
      inversion H₁'.
  Qed.

End test1.
