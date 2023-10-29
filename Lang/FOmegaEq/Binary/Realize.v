Require Import Utf8.
Require FOmegaEq.Kinds.
Require Import FOmegaEq.Types FOmegaEq.Syntax.
Require Import FOmegaEq.Universe FOmegaEq.Interp FOmegaEq.GroundView.
Require Import IxFree.Lib.
Require Import Binding.Intrinsic Binding.Lib Binding.Set.
Require Import FOmegaEq.OpSemantics.
Require Import RelationClasses Morphisms.
Require Import FOmegaEq.Presheaves.
Require Import FOmegaEq.Typing.

Notation "∅" := Empty_set.
Definition vrel := IRel (value ∅ →ₛ value ∅ →ₛ *ₛ)%irel_sig.
Definition erel := IRel (expr ∅ →ₛ expr ∅ →ₛ *ₛ)%irel_sig.

Module BinaryModel <: Point.
  Definition P := vrel.
End BinaryModel.

Module N := GView(BinaryModel).
Export N.

Definition ECC (E : erel) (V : vrel) : erel :=
  λ e₁ e₂, (∃ᵢ v₁ v₂, (e₁ = e_val v₁)ᵢ ∧ᵢ (step e₂ (e_val v₂))ᵢ ∧ᵢ V v₁ v₂) ∨ᵢ
             (∃ᵢ e₁' e₂', (head_step e₁ e₁')ᵢ ∧ᵢ (step e₂ e₂')ᵢ ∧ᵢ ▷ E e₁' e₂').

Lemma ECC_contr V : contractive _ (λ E, ECC E V).
Proof.
  intros R S n; iintro EQ; iintro e₁; iintro e₂; isplit.
  - iintro HR; idestruct HR as HL HR; [now ileft |].
    idestruct HR as e₁' HR; idestruct HR as e₂' HR; idestruct HR as HS₁ HR; idestruct HR as HS₂ HR.
    iright; iexists e₁'; iexists e₂'; isplit; [assumption |]; isplit; [assumption |]; later_shift.
    ispecialize EQ e₁'; ispecialize EQ e₂'; idestruct EQ as EQ EQ'.
    now iapply EQ.
  - iintro HR; idestruct HR as HL HR; [now ileft |].
    idestruct HR as e₁' HR; idestruct HR as e₂' HR; idestruct HR as HS₁ HR; idestruct HR as HS₂ HR.
    iright; iexists e₁'; iexists e₂'; isplit; [assumption |]; isplit; [assumption |]; later_shift.
    ispecialize EQ e₁'; ispecialize EQ e₂'; idestruct EQ as EQ EQ'.
    now iapply EQ'.
Qed.

Definition ECL (V : vrel) : erel := I_fix _ (λ E, ECC E V) (ECC_contr V).

Lemma ECL_cons (V₁ V₂ : vrel) n (HV : n ⊨ V₁ ≾ᵢ V₂) : n ⊨ ECL V₁ ≾ᵢ ECL V₂.
Proof.
  loeb_induction; iintro e₁; iintro e₂; iintro HR.
  apply (I_fix_unroll _ _ (ECC_contr V₁)) in HR; apply (I_fix_roll _ _ (ECC_contr V₂)).
  unfold ECC in *; idestruct HR as HL HR.
  - ileft.
    idestruct HL as v₁ HL; idestruct HL as v₂ HL; idestruct HL as HEQ HL; idestruct HL as HEQ' HL; subst.
    iexists v₁; iexists v₂; isplit; [reflexivity |].
    isplit; [assumption |].
    now iapply HV.
  - iright.
    idestruct HR as e₁' HR; idestruct HR as e₂' HR; idestruct HR as HS₁ HR; idestruct HR as HS₂ HR.
    iexists e₁'; iexists e₂'.
    isplit; [assumption |].
    isplit; [assumption |].
    later_shift.
    now iapply IH.
Qed.

Lemma ECL_step {e₁' e₂ e₂' : expr ∅} {n} {V}
  : OpSemantics.step e₂ e₂'
    -> n ⊨ ECL V e₁' e₂'
    -> n ⊨ ECL V e₁' e₂.
Proof.
  intros HS HE.
  apply (I_fix_unroll _ _ (ECC_contr _)) in HE.
  idestruct HE as HV HE.
  - idestruct HV as v₁ HV;
      idestruct HV as v₂ HV;
      idestruct HV as HEQ HV;
      idestruct HV as HEQ' HV;
      subst.
    apply (I_fix_roll _ _ (ECC_contr _)).
    ileft.
    iexists v₁; iexists v₂.
    isplit; [reflexivity |].
    isplit; [apply Operators_Properties.clos_rt_rt1n_iff |].
    + eapply Relation_Operators.rt_trans.
      eapply Operators_Properties.clos_rt_rt1n_iff, HS.
      eapply Operators_Properties.clos_rt_rt1n_iff, HEQ'.
    + apply HV.
  - idestruct HE as e₁'' HE;
      idestruct HE as e₂'' HE;
      idestruct HE as HS₁ HE;
      idestruct HE as HS₂ HE.
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    iexists e₁''.
    iexists e₂''.
    isplit; [assumption |].
    isplit; [apply Operators_Properties.clos_rt_rt1n_iff |].
    + eapply Relation_Operators.rt_trans.
      eapply Operators_Properties.clos_rt_rt1n_iff, HS.
      eapply Operators_Properties.clos_rt_rt1n_iff, HS₂.
    + apply HE.
Qed.

Lemma ECL_step' {e₁ e₁' e₂ e₂' : expr ∅} {n} {V}
  : OpSemantics.head_step e₁ e₁'
    -> OpSemantics.step e₂ e₂'
    -> n ⊨ ▷ ECL V e₁' e₂'
    -> n ⊨ ECL V e₁ e₂.
Proof.
  intros HS₁ HS₂ HE.
  apply (I_fix_roll _ _ (ECC_contr _)).
  iright.
  eapply I_exists_intro, I_exists_intro.
  isplit; [eassumption |].
  isplit; [eassumption |].
  later_shift.
  apply HE.
Qed.

Lemma ECL_ret {n P v₁ v₂}
  : n ⊨ P v₁ v₂ -> n ⊨ ECL P v₁ v₂.
Proof.
  intros H.
  apply (I_fix_roll _ _ (ECC_contr _)).
  ileft.
  eapply I_exists_intro, I_exists_intro.
  isplit; [reflexivity |].
  isplit; [constructor 1 |].
  assumption.
Qed.

Lemma ECL_ret_inv {n P} {v₁ v₂ : value ∅}
  : n ⊨ ECL P (e_val v₁) (e_val v₂) -> n ⊨ P v₁ v₂.
Proof.
  intros H.
  apply (I_fix_unroll _ _ (ECC_contr _)) in H.
  simpl in H.
  unfold ECC in H.
  idestruct H as H H.
  - idestruct H as v1' H;
      idestruct H as v2' H;
      idestruct H as Hv1 H;
      idestruct H as Hv2 H.
    apply step_val in Hv2.
    inversion Hv1; inversion Hv2; subst.
    apply H.
  - idestruct H as v1' H;
      idestruct H as v2' H;
      idestruct H as Hv1 H;
      idestruct H as Hv2 H.
    exfalso; apply val_head_step in Hv1; apply Hv1.
Qed.

Lemma ECL_bind_l {n P K e₁ e₁' e₂}
  : e₁ ↦ e₁' -> n ⊨ ▷ ECL P (e₁' >>= K)%syn e₂ -> n ⊨ ECL P (e₁ >>= K)%syn e₂.
Proof.
  intros HS H.
  apply (I_fix_roll _ _ (ECC_contr _)).
  iright.
  do 2 eapply I_exists_intro.
  isplit; [constructor; eassumption |].
  isplit; [constructor 1 |].
  later_shift.
  apply H.
Qed.

Lemma ECL_bind_r' {n P K e₁ e₂ e₂'}
  : e₂ ↦* e₂' -> n ⊨ ECL P e₁ (e₂' >>= K)%syn -> n ⊨ ECL P e₁ (e₂ >>= K)%syn.
Proof.
  intros HS H.
  eapply ECL_step.
  eapply ectx_step; eassumption.
  assumption.
Qed.

Lemma ECL_bind {n P P' K₁ K₂ e₁ e₂}
  : n ⊨ (ECL P e₁ e₂ ⇒ (∀ᵢ v₁ v₂, P v₁ v₂ ⇒ ECL P' (v₁ >>= K₁)%syn (v₂ >>= K₂)%syn) ⇒ ECL P' (e₁ >>= K₁)%syn (e₂ >>= K₂)%syn).
Proof.
  irevert e₂; irevert e₁.
  loeb_induction.
  iintro e₁; iintro e₂; iintro H; iintro G.
  apply (I_fix_unroll _ _ (ECC_contr _)) in H.
  idestruct H as H H.
  - idestruct H as v₁ H;
      idestruct H as v₂ H;
      idestruct H as HEQ H;
      idestruct H as HS H.
    subst.
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    do 2 eapply I_exists_intro.
    isplit; [constructor; eassumption |].
    isplit; [constructor 1 |].
    ispecialize_forall G v₁ (value ∅) H.
    ispecialize_forall G v₂ (value ∅) H.
    ispecialize_arrow G; [apply H |].
    apply (I_fix_unroll _ _ (ECC_contr _)) in G.
    idestruct G as G G.
    + idestruct G as v₁' G;
        idestruct G as v₂' G;
        idestruct G as HEQ G;
        idestruct G as HEQ' G.
      inversion HEQ.
    + idestruct G as e₁' G;
        idestruct G as e₂' G;
        idestruct G as HS₁ G;
        idestruct G as HS₂' G.
      later_shift.
      inversion HS₁; subst.
      2: { exfalso; eapply val_head_step; eassumption. }
      eapply ECL_step; [| apply G].
      apply Operators_Properties.clos_rt_rt1n_iff.
      eapply Relation_Operators.rt_trans.
      2: apply Operators_Properties.clos_rt_rt1n_iff in HS₂'; apply HS₂'.
      apply Operators_Properties.clos_rt_rt1n_iff.
      apply ectx_step, HS.
  - idestruct H as e₁' H;
      idestruct H as e₂' H;
      idestruct H as HS₁ H;
      idestruct H as HS₂ H.
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    do 2 eapply I_exists_intro.
    isplit; [constructor; eassumption |].
    isplit; [eapply ectx_step; eassumption |].
    later_shift.
    iapply IH.
    apply H.
    apply G.
Qed.

Lemma ECL_preserve {P : value ∅ -> value ∅ -> Prop}
  (e : expr ∅) v v' n m (H : m < n)
  : nsteps m e (e_val v) -> P v v' -> n ⊨ ECL (fun v v' => (P v v')ᵢ) e (e_val v').
Proof.
  intros G.
  revert H.
  revert n.
  revert G.
  revert e.
  induction m; intros e G n H.
  - inversion G; subst.
    intros J; apply ECL_ret, I_Prop_intro, J.
  - destruct n as [| n'].
    inversion H.
    apply Arith_prebase.lt_S_n in H.
    inversion G; subst.
    intros J.
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    iexists ρ2.
    iexists (e_val v').
    isplit; [assumption |].
    isplit; [constructor 1 |].
    rewrite I_later_shift.
    apply IHm; assumption.
Qed.

Lemma ECL_diverge {P : vrel}
  (e e' e'' : expr ∅) n m (H : n < m)
  : nsteps m e e' -> n ⊨ ECL P e e''.
Proof.
  revert H.
  revert m.
  revert e.
  induction n; intros e m G H.
  - apply Arith_prebase.lt_le_S_stt in G.
    inversion G; subst.
    + inversion H; subst.
      eapply ECL_step'; [eassumption | constructor 1 |].
      apply I_later_zero.
    + inversion H; subst.
      eapply ECL_step'; [eassumption | constructor 1 |].
      apply I_later_zero.
  - destruct m as [| m'].
    inversion G.
    apply Arith_prebase.lt_S_n in G.
    inversion H; subst.
    eapply ECL_step'; [eassumption | constructor 1 |].
    rewrite I_later_shift.
    eapply IHn; eassumption.
Qed.

Lemma ECL_bigstep {P : vrel}
  (e e' e'' : expr ∅) n
  : step e e' -> n ⊨ ECL P e' e'' -> n ⊨ ECL P e e''.
Proof.
  intros HS.
  induction HS.
  - intros G. apply G.
  - intros G.
    eapply ECL_step'; [eassumption | constructor 1 |].
    specialize (IHHS G).
    clear G.
    apply I_later_intro in IHHS.
    assumption.
Qed.

Lemma ECL_safety1 {P : vrel}
  (e t : expr ∅) n
  : n ⊨ ECL P e t ->
    (∃ m v v', (m < S n) ∧ nsteps m e (e_val v) ∧ step t (e_val v') ∧ ((n - m) ⊨ P v v'))
    ∨ (∃ m e', (n < m) ∧ nsteps m e e').
Proof.
  revert e.
  induction n; intros e H.
  - apply (I_fix_unroll _ _ (ECC_contr _)) in H.
    idestruct H as H H.
    + idestruct H as e' H;
        idestruct H as v'' H;
        idestruct H as HS H;
        idestruct H as HEQ H.
      inversion HS; subst.
      left.
      exists 0, e', v''.
      split; [constructor |]; split; [constructor |].
      split; [assumption |].
      inversion HEQ; [subst; assumption | subst].
      assumption.
    + idestruct H as e' H;
        idestruct H as v'' H;
        idestruct H as HS H;
        idestruct H as HEQ H.
      right.
      exists 1, e'.
      split; [constructor | econstructor; [eassumption | constructor]].
  - apply (I_fix_unroll _ _ (ECC_contr _)) in H.
    idestruct H as H H.
    + idestruct H as e' H;
        idestruct H as v'' H;
        idestruct H as HS H;
        idestruct H as HEQ H.
      inversion HS; subst.
      left.
      exists 0, e', v''.
      split; [constructor | split]; [apply le_n_S, le_0_n | constructor |].
      split; [assumption |].
      simpl.
      inversion HEQ; [subst; assumption |].
      assumption.
    + idestruct H as e' H;
        idestruct H as v'' H;
        idestruct H as HS H;
        idestruct H as HEQ H.
      rewrite I_later_shift in H.
      eapply ECL_step in H.
      2: apply HEQ.
      specialize (IHn e' H).
      destruct IHn as [IHn | IHn].
      * destruct IHn as [m [v [t' [H1 [H2 [H3 H4]]]]]].
        left.
        exists (Datatypes.S m), v, t'.
        split; [apply le_n_S; assumption |].
        split; [econstructor 2; eassumption |].
        split; [assumption | assumption].
      * destruct IHn as [m [v [H1 H2]]].
        right.
        exists (Datatypes.S m), v.
        split; [apply le_n_S; assumption |].
        econstructor 2; eassumption.
Qed.

Lemma ECL_safety2' {P : vrel}
  (e t : expr ∅) n
  : (∃ m v v', (m < S n) ∧ nsteps m e (e_val v) ∧ step t (e_val v') ∧ ((n - m) ⊨ P v v'))
    -> n ⊨ ECL P e t.
Proof.
  intros (m & v & v' & Hm & Hs & Hs' & H).
  revert Hs.
  revert H.
  revert Hs'.
  revert e.
  revert Hm.
  revert n.
  induction m; intros n Hm e Hs' H Hs.
  - inversion Hs; subst.
    apply (I_fix_roll _ _ (ECC_contr _)).
    ileft.
    do 2 eapply I_exists_intro.
    isplit; [reflexivity |].
    isplit; [eassumption |].
    rewrite PeanoNat.Nat.sub_0_r in H.
    apply H.
  - inversion Hs; subst.
    apply (I_fix_roll _ _ (ECC_contr _)).
    iright.
    do 2 eapply I_exists_intro.
    isplit; [eassumption |].
    isplit; [constructor 1 |].
    apply Arith_prebase.lt_S_n in Hm.
    simpl in H.
    destruct n as [| n].
    + apply I_later_zero.
    + rewrite I_later_shift.
      apply IHm.
      assumption.
      assumption.
      apply H.
      apply H2.
Qed.

Lemma ECL_safety2 {P : vrel}
  (e t : expr ∅) n
  : (∃ m v v', (m < S n) ∧ nsteps m e (e_val v) ∧ step t (e_val v') ∧ ((n - m) ⊨ P v v'))
    ∨ (∃ m e', (n < m) ∧ nsteps m e e')
    -> n ⊨ ECL P e t.
Proof.
  intros [H | H].
  - destruct H as (m & v & v' & Hm & Hs & Hs' & H).
    apply ECL_safety2'.
    do 3 eexists _.
    split; [eassumption |].
    split; [eassumption |].
    split; [eassumption | eassumption].
  - destruct H as (m & e' & Hm & Hs).
    eapply ECL_diverge; eassumption.
Qed.

Lemma ECL_safety {P : vrel}
  (e t : expr ∅) n
  : (n ⊨ ECL P e t) <->
      (∃ m v v', (m < S n) ∧ nsteps m e (e_val v) ∧ step t (e_val v') ∧ ((n - m) ⊨ P v v'))
      ∨ (∃ m e', (n < m) ∧ nsteps m e e').
Proof.
  split.
  - apply ECL_safety1.
  - apply ECL_safety2.
Qed.

Lemma ECL_partial_correctness {P : vrel}
  (e t : expr ∅) n
  : n ⊨ ECL P e t -> (∀ m v v', (m < S n) -> nsteps m e (e_val v) -> step t (e_val v') -> ((n - m) ⊨ P v v')).
Proof.
  intros H m.
  revert H.
  revert n.
  revert e t.
  induction m; intros e t n H v v' Hm Hs Hs'.
  - inversion Hs; subst.
    apply (I_fix_unroll _ _ (ECC_contr _)) in H.
    idestruct H as H H.
    + idestruct H as w H;
        idestruct H as w' H;
        idestruct H as Hw H;
        idestruct H as Hw' H.
      inversion Hw; subst.
      assert (v' = w') as ->.
      {
        eapply step_det in Hw'; [| apply Hs'].
        destruct Hw' as [Hw' | Hw']; [inversion Hw'; reflexivity |].
        apply step_val in Hw'.
        inversion Hw'; reflexivity.
      }
      rewrite PeanoNat.Nat.sub_0_r.
      apply H.
    + idestruct H as w H;
        idestruct H as w' H;
        idestruct H as Hw H.
      apply val_head_step in Hw.
      contradiction.
  - inversion Hs as [ | ? ? ? ? Hstep ]; subst.
    apply (I_fix_unroll _ _ (ECC_contr _)) in H.
    idestruct H as H H.
    + idestruct H as w H;
        idestruct H as w' H;
        idestruct H as Hw H;
        idestruct H as Hw' H.
      inversion Hw; subst.
      apply val_head_step in Hstep.
      contradiction.
    + destruct n as [| n].
      * apply Arith_prebase.lt_S_n in Hm.
        inversion Hm.
      * simpl.
        idestruct H as w H;
          idestruct H as w' H;
          idestruct H as Hw H;
          idestruct H as Hw' H.
        eapply head_step_det in Hstep; [| apply Hw].
        subst.
        eapply IHm.
        rewrite I_later_shift in H.
        apply H.
        apply PeanoNat.Nat.succ_lt_mono; assumption.
        assumption.
        eapply step_det in Hw'; [| apply Hs'].
        destruct Hw' as [Hw' | Hw']; [inversion Hw'; constructor 1 | apply Hw'].
Qed.

(** Fig. 19. Like in the unary case, needs to be taken as a
    step-indexed fixpoint *)
Program Fixpoint RPR (RP : gtyp → vrel) (g : gtyp) : vrel :=
  match g with
  | GAbstract P => P
  | GUnit => λ v₁ v₂, (v₁ = v_unit)ᵢ ∧ᵢ (v₂ = v_unit)ᵢ
  | GVoid => λ _ _, (False)ᵢ
  | GProd g1 g2 => λ v₁ v₂,
      (∃ᵢ va vb vc vd, (v₁ = v_pair va vb)ᵢ ∧ᵢ (v₂ = v_pair vc vd)ᵢ ∧ᵢ RPR RP g1 va vc ∧ᵢ RPR RP g2 vb vd)
  | GSum g1 g2 => λ v₁ v₂,
      (∃ᵢ va vb, (v₁ = v_inj L va)ᵢ ∧ᵢ (v₂ = v_inj L vb)ᵢ ∧ᵢ RPR RP g1 va vb) ∨ᵢ (∃ᵢ va vb, (v₁ = v_inj R va)ᵢ ∧ᵢ (v₂ = v_inj R vb)ᵢ ∧ᵢ RPR RP g2 va vb)
  | GArr g1 g2 => λ v₁ v₂,
      (∀ᵢ u₁ u₂, RPR RP g1 u₁ u₂ ⇒ ECL (RPR RP g2) (e_app v₁ u₁) (e_app v₂ u₂))
  | GAll κ φ => λ v₁ v₂,
      (∃ᵢ e₁ e₂, (v₁ = v_tlam e₁)ᵢ ∧ᵢ (v₂ = v_tlam e₂)ᵢ ∧ᵢ
               ∀ᵢ (μ : kint κ ε),
         (sub_rel η_id μ μ)ᵢ ⇒
           ▷ ECL (RP (viewG (interpNf φ η_id ε ı%bind μ))) e₁ e₂)
  | GXist κ φ => λ v₁ v₂,
      (∃ᵢ va vb, (v₁ = v_pack va)ᵢ ∧ᵢ (v₂ = v_pack vb)ᵢ ∧ᵢ
                   ∃ᵢ (μ : kint κ ε), (sub_rel η_id μ μ)ᵢ ∧ᵢ
                                        ▷ RP (viewG (interpNf φ η_id _ ı%bind μ)) va vb)
  | GRec κ φ η EQ => λ v₁ v₂,
      (∃ᵢ va vb, (v₁ = v_roll va)ᵢ ∧ᵢ (v₂ = v_roll vb)ᵢ ∧ᵢ
                ▷ RP (viewG (match fkm_pkt' _ _ EQ in _ = κ return kint κ ε → kint Kinds.KTyp ε with
                             | eq_refl => applyAll (F := λ κ, kint κ ε) (List.map pkt' η)
                             end
                               (interpNf φ η_id ε ı%bind (interpNeu (neu_app (neu_ctor (Kinds.tc_rec κ)) φ) η_id)))) va vb)
  | GCArr χ g => λ v₁ v₂, (ctrue χ)ᵢ ⇒ ECL (RPR RP g) (e_capp v₁) (e_capp v₂)
  | GCPrd χ g => λ v₁ v₂, ∃ᵢ va vb, (v₁ = v_withC va ∧ v₂ = v_withC vb ∧ ctrue χ)ᵢ ∧ᵢ RPR RP g va vb
  end.

Lemma RPR_contr : contractive (gtyp →ₛ value ∅ →ₛ value ∅ →ₛ *ₛ)%irel_sig RPR.
Proof.
  intros R S n; iintro EQ; iintro g; induction g; iintro v₁; iintro v₂.
  - simpl; creflexivity.
  - simpl; creflexivity.
  - simpl; creflexivity.
  - simpl; isplit; iintro HR; idestruct HR as va HR; idestruct HR as vb HR; idestruct HR as vc HR; idestruct HR as vd HR; idestruct HR as EQ' HR; idestruct HR as HL HR; subst.
    + idestruct HR as HR₁ HR₂.
      iexists va; iexists vb; iexists vc; iexists vd; isplit; [reflexivity | isplit; [reflexivity |]].
      ispecialize IHg1 va; ispecialize IHg1 vc; ispecialize IHg2 vb; ispecialize IHg2 vd;
        idestruct IHg1 as HH HH'; idestruct IHg2 as HG HG';
        isplit; [now iapply HH | now iapply HG].
    + idestruct HR as HR₁ HR₂.
      iexists va; iexists vb; iexists vc; iexists vd; isplit; [reflexivity | isplit; [reflexivity |]].
      ispecialize IHg1 va; ispecialize IHg1 vc; ispecialize IHg2 vb; ispecialize IHg2 vd;
          idestruct IHg1 as HH HH'; idestruct IHg2 as HG HG';
          isplit; [now iapply HH' | now iapply HG'].
  - simpl; isplit; iintro HR; idestruct HR as HR HR; idestruct HR as va HR; idestruct HR as vb HR;
      idestruct HR as HH HR; idestruct HR as HH' HR; subst.
    + ileft; iexists va; iexists vb; isplit; [reflexivity | isplit; [reflexivity |]].
      ispecialize IHg1 va; ispecialize IHg1 vb; idestruct IHg1 as HH HH'.
      now iapply HH.
    + iright; iexists va; iexists vb; isplit; [reflexivity | isplit; [reflexivity |]].
      ispecialize IHg2 va; ispecialize IHg2 vb; idestruct IHg2 as HH HH'.
      now iapply HH.
    + ileft; iexists va; iexists vb; isplit; [reflexivity | isplit; [reflexivity |]].
      ispecialize IHg1 va; ispecialize IHg1 vb; idestruct IHg1 as HH HH'.
      now iapply HH'.
    + iright; iexists va; iexists vb; isplit; [reflexivity | isplit; [reflexivity |]].
      ispecialize IHg2 va; ispecialize IHg2 vb; idestruct IHg2 as HH HH'.
      now iapply HH'.
  - simpl; isplit; iintro HR; iintro u₁; iintro u₂; iintro HU.
    + iapply ECL_cons; [| iapply HR].
      * iintro w₁; iintro w₂; iintro HW; ispecialize IHg2 w₁; ispecialize IHg2 w₂; idestruct IHg2 as HH HH'; now iapply HH.
      * ispecialize IHg1 u₁; ispecialize IHg1 u₂; idestruct IHg1 as HH HH'; now iapply HH'.
    + iapply ECL_cons; [| iapply HR].
      * iintro w₁; iintro w₂; iintro HW; ispecialize IHg2 w₁; ispecialize IHg2 w₂; idestruct IHg2 as HH HH'; now iapply HH'.
      * ispecialize IHg1 u₁; ispecialize IHg1 u₂; idestruct IHg1 as HH HH'; now iapply HH.
  - simpl; isplit; iintro HR; idestruct HR as e₁ HR; idestruct HR as e₂ HR;
      idestruct HR as EQ' HR; idestruct HR as EQ'' HR; subst;
      iexists e₁; iexists e₂; (isplit; [reflexivity | isplit; [reflexivity |]]);
      iintro μ; iintro HH; ispecialize HR μ;
      (ispecialize HR; [assumption | later_shift]).
    + iapply ECL_cons; [| exact HR].
      iintro u₁; iintro u₂; ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)).
      ispecialize EQ u₁; ispecialize EQ u₂; now idestruct EQ as EQ1 EQ2.
    + iapply ECL_cons; [| exact HR].
      iintro u₁; iintro u₂; ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)).
      ispecialize EQ u₁; ispecialize EQ u₂; now idestruct EQ as EQ1 EQ2.
  - simpl; isplit; iintro HR; idestruct HR as v₁' HR; idestruct HR as v₂' HR;
      idestruct HR as EQ' HR; idestruct HR as EQ'' HR; subst;
      idestruct HR as μ HR; idestruct HR as HH HR;
      iexists v₁'; iexists v₂'; (isplit; [reflexivity | isplit; [reflexivity |]]);
      iexists μ; (isplit; [assumption | later_shift]).
    + ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)); ispecialize EQ v₁'; ispecialize EQ v₂'.
      idestruct EQ as EQ1 EQ2; now iapply EQ1.
    + ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)); ispecialize EQ v₁'; ispecialize EQ v₂'.
      idestruct EQ as EQ1 EQ2; now iapply EQ2.
  - simpl; isplit; iintro HR; idestruct HR as v₁' HR; idestruct HR as v₂' HR;
      idestruct HR as EQ' HR; idestruct HR as EQ'' HR; subst;
      iexists v₁'; iexists v₂'; (isplit; [reflexivity | isplit; [reflexivity |]]); later_shift.
    + ispecialize EQ (viewG
                        (match fkm_pkt' (fkind Kinds.KTyp η) η eq_refl in (_ = κ) return kint κ ε → kint Kinds.KTyp ε with
                         | eq_refl => applyAll (F := λ κ, kint κ ε) (List.map pkt' η)
                         end
                           (interpNf μ η_id ε ı%bind (interpNeu (neu_app (neu_ctor (Kinds.tc_rec (fkind _ η))) μ) η_id))));
        ispecialize EQ v₁'; ispecialize EQ v₂'.
      idestruct EQ as EQ1 EQ2; now iapply EQ1.
    + ispecialize EQ (viewG
                        (match fkm_pkt' (fkind Kinds.KTyp η) η eq_refl in (_ = κ) return kint κ ε → kint Kinds.KTyp ε with
                         | eq_refl => applyAll (F := λ κ, kint κ ε) (List.map pkt' η)
                         end
                           (interpNf μ η_id ε ı%bind (interpNeu (neu_app (neu_ctor (Kinds.tc_rec (fkind _ η))) μ) η_id))));
        ispecialize EQ v₁'; ispecialize EQ v₂'.
      idestruct EQ as EQ1 EQ2; now iapply EQ2.
  - simpl; isplit; iintro HR; iintro HH.
    + iapply ECL_cons; [| now iapply HR].
      iintro u₁; iintro u₂; ispecialize IHg u₁; ispecialize IHg u₂; now idestruct IHg as HH1 HH2.
    + iapply ECL_cons; [| now iapply HR].
      iintro u₁; iintro u₂; ispecialize IHg u₁; ispecialize IHg u₂; now idestruct IHg as HH1 HH2.
  - simpl; isplit; iintro HR;
      idestruct HR as u₁ HR; idestruct HR as u₂ HR; idestruct HR as HH HR; destruct HH as [? [? HH]]; subst.
    + iexists u₁; iexists u₂; isplit; [now split |].
      ispecialize IHg u₁; ispecialize IHg u₂; idestruct IHg as HG HG'; now iapply HG.
    + iexists u₁; iexists u₂; isplit; [now split |].
      ispecialize IHg u₁; ispecialize IHg u₂; idestruct IHg as HG HG'; now iapply HG'.
Qed.

Definition RP := I_fix (gtyp →ₛ value ∅ →ₛ value ∅ →ₛ *ₛ)%irel_sig RPR RPR_contr.

Definition logrelV {X : Set} (Δ : Ctx Kinds.kind) (Ψ : list (constr Δ)) (Γ : X → typ Kinds.KTyp Δ)
  (v₁ v₂ : value X) (τ : typ Kinds.KTyp Δ) :=
  ∀ (η : NSub Δ ε) (Rη : sub_relS η_id η η) (HH : ∀ ψ, List.In ψ Ψ → ctrue (interpC ψ η)),
  ∀ (γ γ' : X [⇒] ∅) n (HG : n ⊨ ∀ᵢ x, RP (viewG (interp (Γ x) η)) (γ x) (γ' x)),
  n ⊨ RP (viewG (interp τ η)) (bind γ v₁) (bind γ' v₂).

Definition logrelE {X : Set} (Δ : Ctx Kinds.kind) (Ψ : list (constr Δ)) (Γ : X → typ Kinds.KTyp Δ)
  (e₁ e₂ : expr X) (τ : typ Kinds.KTyp Δ) :=
  ∀ (η : NSub Δ ε) (Rη : sub_relS η_id η η) (HH : ∀ ψ, List.In ψ Ψ → ctrue (interpC ψ η)),
  ∀ (γ γ' : X [⇒] ∅) n (HG : n ⊨ ∀ᵢ x, RP (viewG (interp (Γ x) η)) (γ x) (γ' x)),
  n ⊨ ECL (RP (viewG (interp τ η))) (bind γ e₁) (bind γ' e₂).

Lemma logrelE_fmap {V₁ V₂ : Set} {Δ : Ctx Kinds.kind} {Ψ : list (constr Δ)}
  (Γ₁ : V₁ -> typ Kinds.KTyp Δ) (Γ₂ : V₂ -> typ Kinds.KTyp Δ)
  (e e' : expr V₁) (τ : typ Kinds.KTyp Δ)
  (δ : Binding.Set.Arr V₁ V₂)
  (EQ : ∀ x, Γ₁ x = (Env.compose Γ₂ δ) x)
  (HT : logrelE Δ Ψ Γ₁ e e' τ)
  : logrelE Δ Ψ Γ₂ (fmap δ e) (fmap δ e') τ
with
logrelV_fmap {V₁ V₂ : Set} {Δ : Ctx Kinds.kind} {Ψ : list (constr Δ)}
  (Γ₁ : V₁ -> (typ Kinds.KTyp Δ)) (Γ₂ : V₂ -> (typ Kinds.KTyp Δ))
  (v v' : value V₁) (τ : typ Kinds.KTyp Δ)
  (δ : Binding.Set.Arr V₁ V₂)
  (EQ : ∀ x, Γ₁ x = (Env.compose Γ₂ δ) x)
  (HT : logrelV Δ Ψ Γ₁ v v' τ)
  : logrelV Δ Ψ Γ₂ (fmap δ v) (fmap δ v') τ.
Proof.
  - intros η Hη HΨ γ γ' n Hγ.
    rewrite ->2 (map_to_bind δ).
    rewrite ->2 bind_bind_comp'.
    apply HT; [assumption | assumption |].
    iintro x; term_simpl.
    rewrite EQ.
    iapply Hγ.
  - intros η Hη HΨ γ γ' n Hγ.
    rewrite ->2 (map_to_bind δ).
    rewrite ->2 bind_bind_comp'.
    apply HT; [assumption | assumption |].
    iintro x; term_simpl.
    rewrite EQ.
    iapply Hγ.
Qed.

Lemma logrelE_fmap_types {V : Set} {Δ Δ' Ξ} {Γ : V -> typ Kinds.KTyp Δ} {e e' τ}
  (f : Binding.Intrinsic.Arr Δ Δ')
  (HT : logrelE Δ Ξ Γ e e' τ)
  : logrelE Δ' (List.map (fmap f) Ξ) (Env.compose (fmap f) Γ) e e' (fmap f τ)
with logrelV_fmap_types {V : Set} {Δ Δ' Ξ} {Γ : V -> typ Kinds.KTyp Δ} {v v' τ}
       (f : Binding.Intrinsic.Arr Δ Δ')
       (HT : logrelV Δ Ξ Γ v v' τ)
  : logrelV Δ' (List.map (fmap f) Ξ) (Env.compose (fmap f) Γ) v v' (fmap f τ).
Proof.
  - intros η Hη HΨ γ γ' n Hγ.
    specialize (HT (precomp_sub η f)).
    assert (∀ τ : typ Kinds.KTyp Δ, 〚 fmap f τ 〛 η ≅ 〚 τ 〛 precomp_sub η f) as HEQ.
    {
      intros τ'.
      apply interp_map; intros; unfold precomp_sub; simpl.
      reflexivity.
    }
    rewrite HEQ.
    apply HT.
    + intros ? ? ?; unfold precomp_sub; simpl; apply Hη.
    + intros ψ HIn.
      apply (List.in_map (fmap f)) in HIn.
      specialize (HΨ (fmap f ψ) HIn).
      erewrite interpC_map in HΨ.
      eapply HΨ.
      intros; unfold precomp_sub; simpl; reflexivity.
    + iintro x.
      rewrite <-HEQ.
      iapply Hγ.
  - intros η Hη HΨ γ γ' n Hγ.
    specialize (HT (precomp_sub η f)).
    assert (∀ τ : typ Kinds.KTyp Δ, 〚 fmap f τ 〛 η ≅ 〚 τ 〛 precomp_sub η f) as HEQ.
    {
      intros τ'.
      apply interp_map; intros; unfold precomp_sub; simpl.
      reflexivity.
    }
    rewrite HEQ.
    apply HT.
    + intros ? ? ?; unfold precomp_sub; simpl; apply Hη.
    + intros ψ HIn.
      apply (List.in_map (fmap f)) in HIn.
      specialize (HΨ (fmap f ψ) HIn).
      erewrite interpC_map in HΨ.
      eapply HΨ.
      intros; unfold precomp_sub; simpl; reflexivity.
    + iintro x.
      rewrite <-HEQ.
      iapply Hγ.
Qed.
