Require Import Utf8.
Require Import Lang.FOmegaEq.Types Lang.FOmegaEq.Kinds Lang.FOmegaEq.Syntax Lang.FOmegaEq.OpSemantics Lang.FOmegaEq.Typing.
Require Import FOmegaEq.Interp FOmegaEq.Universe.
Import Binding.Intrinsic (Ctx, dom, extC, Build_Ctx, mtC).
Require Import Binding.Lib Binding.Env.
Import kindEqDec.
Require Import Coq.Relations.Relation_Operators Coq.Relations.Operators_Properties.

Local Hint Constructors tctd : core.

Module Model <: Point.
  Definition P := False.
End Model.

Module N := Interp(Model).
Export N.

Ltac cdiscrK :=
  unfold cdiscrK;
  match goal with
  | [ |- match eq_dec ?κ1 ?κ2 with
         | left EQ => ?H1
         | right _ => ?H2
         end ?c1 ?c2 ] => destruct (eq_dec κ1 κ2) as [EQ | _];
                          [inversion EQ; subst; try rewrite UIP_refl with (p := EQ); simpl; try econstructor | exact I]
  end.

Local Hint Extern 0 (cdiscrK _ _) => cdiscrK : core.

Lemma rel_app_constrL {Δ : Ctx kind} {κ1 κ2 κ} τ1 τ2 σ1 σ2 t
  (HF : rel_app κ1 τ1 τ2 κ2 σ1 σ2)
  (tc : @tctd Δ _ τ1 κ t) : @tctd Δ _ σ1 κ t.
Proof.
  induction HF.
  - assumption.
  - apply inj_app.
    apply IHHF.
Qed.

Lemma rel_app_constrR {Δ : Ctx kind} {κ1 κ2 κ} τ1 τ2 σ1 σ2 t
  (HF : rel_app κ1 τ1 τ2 κ2 σ1 σ2)
  (tc : @tctd Δ _ τ2 κ t) : @tctd Δ _ σ2 κ t.
Proof.
  induction HF.
  - assumption.
  - apply inj_app.
    apply IHHF.
Qed.

Local Open Scope syn_scope.

(* Lemma 4.2; other canonical forms lemmas follow *)
Lemma canArr {τ τ1 τ2 Γ} {v : value ∅}
      (HP : tequiv nil τ (τ1 →ᵗ τ2)%typ)
      (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ)
  : (∃ e, v = ƛ e ∧  mtC ∣ nil ∣ Γ ▹ τ1 ⊢ₑ e : τ2)
    \/ (∃ e, v = rec e ∧  mtC ∣ nil ∣ Γ ▹ (τ1 →ᵗ τ2) ▹ τ1 ⊢ₑ e : τ2).
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 6 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [| |].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - left.
    eexists; split; [reflexivity |].
    eapply T_congE, etypes_equiv_ctx, H.
    + eapply tpi_appInjR, HP; auto.
    + intros [| []]; simpl; eapply tpi_appInjR, tpi_appInjL, HP; auto.
  - right.
    eexists; split; [reflexivity |].
    eapply T_congE, etypes_equiv_ctx, H.
    + eapply tpi_appInjR, HP; auto.
    + intros [| []]; simpl; [| apply HP | now trivial].
      eapply tpi_appInjL, tpi_appInjR in HP; eauto.
Qed.

Lemma canTArr {κ τ τ' Γ} {v : value ∅}
  (HP : tequiv nil τ (∀ᵗ κ, τ')%typ)
  (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ)
  : ∃ e, v = Λ e ∧ _ ∣ nil ∣ shift • Γ ⊢ₑ e : τ'.
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [|].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - eexists; split; [reflexivity |].
    destruct (eq_dec κ0 κ) as [EQ | NEq]; [subst κ0 |].
    + eapply T_congE, H.
      eapply tpi_appInjR in HP; auto.
      apply tproves_i_lam, HP.
    + apply consistency in HP; [now trivial |].
      eapply td_ctd; [eauto using @tctd .. | cdiscrK].
      now contradiction NEq.
Qed.

Lemma canProd {τ τ1 τ2 v} {Γ : ∅ → typ ⋆ mtC}
      (HP : tequiv nil τ (τ1 × τ2)%typ)
      (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  ∃ v1 v2, v = ⟨v1, v2⟩ ∧ mtC ∣ nil ∣ Γ ⊢ᵥ v1 : τ1 ∧ mtC ∣ nil ∣ Γ ⊢ᵥ v2 : τ2.
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [|].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - eexists; eexists; split; [reflexivity |].
    split; (eapply T_congV; [| eassumption]).
    + eapply tpi_appInjL, tpi_appInjR in HP; now eauto using @tctd.
    + eapply tpi_appInjR in HP; now eauto using @tctd.
Qed.

Lemma canVoid {τ v} {Γ : ∅ → typ ⋆ mtC}
      (HP : tequiv nil τ ⊥%typ)
      (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  False.
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [].
  apply IHHT; [reflexivity .. | etransitivity; eassumption].
Qed.

Lemma canSum {τ τ1 τ2} {v} {Γ : ∅ → typ ⋆ mtC}
  (HP : tequiv nil τ (τ1 + τ2)%typ)
  (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  (∃ v1, v = v_inj L v1 ∧ mtC ∣ nil ∣ Γ ⊢ᵥ v1 : τ1) ∨
  (∃ v2, v = v_inj R v2 ∧ mtC ∣ nil ∣ Γ ⊢ᵥ v2 : τ2).
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [| |].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - left; eexists; split; [reflexivity |].
    eapply T_congV, HT.
    eapply tpi_appInjL, tpi_appInjR in HP; now eauto using @tctd.
  - right; eexists; split; [reflexivity |].
    eapply T_congV, HT.
    eapply tpi_appInjR in HP; now eauto using @tctd.
Qed.

Lemma canXist {κ τ} {τ' : typ ⋆ (extC κ mtC)} {v} {Γ : ∅ → typ ⋆ mtC}
      (HP : tequiv nil τ (∃ᵗ κ, τ')%typ)
      (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  ∃ v', v = v_pack v' ∧ ∃ σ, mtC ∣ nil ∣ Γ ⊢ᵥ v' : subst τ' σ.
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [|].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - destruct (eq_dec κ κ0) as [EQκ | NEQ]; [subst κ0 |].
    + eexists; split; [reflexivity |].
      exists τ'0; eapply T_congV, HT.
      eapply tpi_trans, tpi_beta.
      eapply tpi_trans; [apply tpi_symm, tpi_beta |].
      apply tpi_app; [| now change (tequiv nil τ'0 τ'0)].
      eapply tpi_appInjR, HP; eauto using @tctd.
    + apply consistency in HP; [now trivial |].
      eapply td_ctd; [now eauto using @tctd .. | cdiscrK].
      now contradiction NEQ.
Qed.

Lemma canCArr {τ τ' φ} {v} {Γ : ∅ → typ ⋆ mtC}
  (HP : tequiv nil τ (φ →ᶜ τ')%typ)
  (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  ∃ e, v = ƛᶜ e ∧ (nil ⊩ φ → mtC ∣ nil ∣ Γ ⊢ₑ e : τ').
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [|].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - eexists; split; [reflexivity | intros HP'].
    eapply T_congE, (constr_cut_expr (Ψ₁ := nil) (Ψ₂ := φ0 :: nil) (Ψ₃ := nil)), H.
    + eapply tpi_carrInjR, HP.
    + simpl; intros φ1 [[] | []]; clear φ1.
      eapply tpi_carrInjL, HP'.
      apply tpi_symm, HP.
Qed.

Lemma canCProd {τ τ' φ} {v} {Γ : ∅ → typ ⋆ mtC}
  (HP : tequiv nil τ (φ ×ᶜ τ')%typ)
  (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  ∃ v', v = ⟨v'⟩ᶜ ∧ mtC ∣ nil ∣ Γ ⊢ᵥ v' : τ' ∧ nil ⊩ φ.
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [|].
  - apply IHHT; [reflexivity .. | etransitivity; eassumption].
  - eexists; split; [reflexivity | split].
    + eapply T_congV, HT.
      eapply tpi_cprodInjR, HP.
    + eapply tpi_cprodInjL, H; eassumption.
Qed.

Require Import List.

Lemma rel_app_shape {Δ : Ctx kind} {κ1 κ2} τ1 τ2 σ1 σ2
      (HF : @rel_app Δ κ1 τ1 τ2 κ2 σ1 σ2) :
  exists κs : list kind, fold_left (λ κᵣ κₐ, KArr κₐ κᵣ)  κs κ2 = κ1.
Proof.
  induction HF; [exists nil; reflexivity |].
  destruct IHHF as [κs EQ].
  exists (κₐ :: κs); simpl; apply EQ.
Qed.

Lemma fold_right_ctor κs κ :
  fold_right KArr κ κs = κ -> κs = nil.
Proof.
  revert κs; induction κ; intros; simpl in *.
  - destruct κs; [reflexivity | simpl in H; discriminate].
  - rewrite <- rev_involutive with (l := κs), fold_left_rev_right in H.
    change (fold_left (λ x y : kind, y ⇒ x) (κ1 :: rev κs) κ2 = κ1 ⇒ κ2) in H.
    rewrite <- fold_left_rev_right in H; simpl in H; rewrite rev_involutive in H.
    destruct κs; [reflexivity | exfalso]; simpl in H.
    inversion H; subst; clear H.
    apply IHκ2 in H2; symmetry in H2; now apply app_cons_not_nil in H2.
Qed.

Lemma fold_right_ctor_eq κs1 κs2 κ :
  fold_right KArr κ κs1 = fold_right KArr κ κs2 -> κs1 = κs2.
Proof.
  revert κ κs2; induction κs1; intros; simpl in *.
  - symmetry in H; apply fold_right_ctor in H; now subst.
  - destruct κs2; simpl in *.
    + now apply fold_right_ctor with (κs := a :: κs1) in H.
    + inversion H; subst; clear H; f_equal.
      eapply IHκs1, H2.
Qed.

Lemma relApp_det {Δ κ κ₁ κ₂} {μ₁ μ₂ ν₁ ν₂ : typ κ₁ Δ} {σ₁ σ₂ τ₁ τ₂ : typ κ₂ Δ} (c : tctor κ)
      (HC1 : tctd μ₁ c) (HC2 : tctd ν₁ c)
      (HR1 : rel_app κ₁ μ₁ μ₂ κ₂ σ₁ σ₂)
      (HR2 : rel_app κ₁ ν₁ ν₂ κ₂ τ₁ τ₂)
      (HP : tequiv nil σ₁ τ₁) :
  (tequiv nil μ₂ ν₂ → tequiv nil σ₂ τ₂) ∧ tequiv nil μ₁ ν₁.
Proof.
  revert τ₁ τ₂ HR2 HP; induction HR1; intros.
  - inversion HR2; subst.
    + apply inj_pairT2 in H1; subst.
      apply inj_pairT2 in H2; subst.
      split; [now trivial | assumption].
    + apply inj_pairT2 in H1; subst.
      apply inj_pairT2 in H2; subst.
      apply rel_app_shape in HF; destruct HF as [κs EQ].
      change (fold_left  (λ κᵣ κₐ, κₐ ⇒ κᵣ) (κₐ :: κs) κ₁ = κ₁) in EQ.
      rewrite <- fold_left_rev_right in EQ; apply fold_right_ctor in EQ.
      simpl in EQ; symmetry in EQ; now apply app_cons_not_nil in EQ.
  - inversion HR2; subst.
    + apply inj_pairT2 in H4; subst.
      apply inj_pairT2 in H2; subst.
      apply rel_app_shape in HR1; destruct HR1 as [κs EQ].
      change (fold_left  (λ κᵣ κₐ, κₐ ⇒ κᵣ) (κₐ :: κs) κᵣ = κᵣ) in EQ.
      rewrite <- fold_left_rev_right in EQ; apply fold_right_ctor in EQ.
      simpl in EQ; symmetry in EQ; now apply app_cons_not_nil in EQ.
    + apply inj_pairT2 in H1; subst.
      apply inj_pairT2 in H2; subst.
      assert (EQ1 : exists κs : list kind, fold_left (λ κᵣ κₐ, KArr κₐ κᵣ) (κₐ0 :: κs) κᵣ = κ₁)
        by (simpl; eapply rel_app_shape, HF).
      assert (EQ2 : exists κs : list kind, fold_left (λ κᵣ κₐ, KArr κₐ κᵣ) (κₐ :: κs) κᵣ = κ₁)
        by (simpl; eapply rel_app_shape, HR1).
      destruct EQ1 as [κs EQ1], EQ2 as [κs' EQ2]; rewrite <- EQ2 in EQ1.
      rewrite <- !fold_left_rev_right in EQ1; apply fold_right_ctor_eq in EQ1.
      apply f_equal with (f := @rev _) in EQ1; rewrite !rev_involutive in EQ1.
      inversion EQ1; clear EQ1 EQ2; subst.
      edestruct IHHR1 as [HH HEQ]; [eassumption | |].
      * eapply tpi_appInjL, HP; eauto using rel_app_constrL.
      * split; [intros HE | assumption].
        apply tpi_app; [apply HH, HE |].
        eapply tpi_appInjR, HP; eauto using rel_app_constrL.
Qed.

Lemma canRec {κ} {τ τ' σ} {μ : typ κ (extC κ mtC)} {v} {Γ : ∅ → typ ⋆ mtC}
      (HP : tequiv nil τ τ')
      (HF : rel_app κ (rec_type mtC κ μ) (subst (F := typ κ) μ (rec_type mtC κ μ)) ⋆ τ' σ)
      (HT : mtC ∣ nil ∣ Γ ⊢ᵥ v : τ) :
  ∃ v', v = v_roll v' ∧ mtC ∣ nil ∣ Γ ⊢ᵥ v' : σ.
Proof.
  remember ∅ as X eqn: EQX; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; [now destruct x |
                        try (apply consistency in HP; [now trivial | now eauto 7 using @tdiscr, @tctd, @cdiscr, rel_app_constrL]) ..]; [|].
  - eapply IHHT; [reflexivity .. | etransitivity; eassumption | eassumption].
  - destruct (eq_dec κ κ0) as [EQ | NEQ]; [subst κ0 |].
    + eexists; split; [reflexivity |].
      eapply T_congV, HT.
      edestruct (@relApp_det) as [HH HEQ]; [| | exact HF0 | exact HF | exact HP |];
        [eauto using @tctd .. |].
      eapply tpi_appInjR, tproves_i_lam in HEQ; [| constructor ..].
      eapply HH, tpi_trans, tpi_beta.
      eapply tpi_trans; [apply tpi_symm, tpi_beta |].
      apply tpi_app, tpi_app, tpi_lam, HEQ; [apply tpi_lam, HEQ | apply tpi_ctor].
    + apply consistency in HP; [now trivial |].
      eapply td_ctd; [now eauto using @tctd, rel_app_constrL .. | cdiscrK].
      now contradiction NEQ.
Qed.

(** Lemma 4.4 *)
Lemma progress e τ (Γ : ∅ → typ ⋆ mtC) (HT : mtC ∣ nil ∣ Γ ⊢ₑ e : τ) :
  (∃ e', head_step e e') ∨ (∃ v, e = e_val v).
Proof.
  change e with (eq_rect_r expr e eq_refl).
  generalize (eq_refl (x := ∅)) as EQ; revert e Γ HT.
  generalize ∅ at 1 2 3 5 8 13 as X; intros.
  remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; unfold eq_rect_r in *; simpl in *.
  - right; now eexists.
  - left; unshelve edestruct IHHT1 as [[e' HR] | [v EQ]];
      [reflexivity .. | | simpl in *; subst]; now eauto using @head_step.
  - now apply IHHT with (EQ := eq_refl (x := ∅)).
  - left; eapply canArr in H; [| unfold t_arr; reflexivity].
    destruct H as [H | H].
    + destruct H as [e [EQ _]]; subst v₁; now eauto using @head_step.
    + destruct H as [e [EQ _]]; subst v₁; now eauto using @head_step.
  - left; eapply canTArr in H; [| unfold t_all; reflexivity].
    destruct H as [e [EQ _]]; subst; now eauto using @head_step.
  - left; eapply canProd in H; [| unfold t_prod; reflexivity].
    destruct H as [e1 [e2 [EQ _]]]; subst; now eauto using @head_step.
  - left; eapply canProd in H; [| unfold t_prod; reflexivity].
    destruct H as [e1 [e2 [EQ _]]]; subst; now eauto using @head_step.
  - now apply canVoid in H.
  - left; eapply canSum in H; [| unfold t_sum; reflexivity].
    destruct H as [[v1 [EQ _]] | [v2 [EQ _]]]; subst; now eauto using @head_step.
  - eapply canXist in H; [| unfold t_xist; reflexivity].
    destruct H as [v' [EQ _]]; subst; now eauto using @head_step.
  - eapply canRec in H; [| reflexivity | eassumption].
    destruct H as [v' [EQ _]]; subst; now eauto using @head_step.
  - now apply consistency in H.
  - left; eapply canCArr in H0; [| reflexivity].
    destruct H0 as [e [EQ _]]; subst; now eauto using @head_step.
  - left; eapply canCProd in H; [| reflexivity].
    destruct H as [v' [EQ _]]; subst; now eauto using @head_step.
Qed.

(** Lemma 4.3 *)
Lemma preservation e e' τ (Γ : ∅ → typ ⋆ mtC)
      (HT : mtC ∣ nil ∣ Γ ⊢ₑ e : τ)
      (HR : e ↦ e')
  : mtC ∣ nil ∣ Γ ⊢ₑ e' : τ.
Proof.
  change (eq_rect_r expr e eq_refl ↦ eq_rect_r expr e' eq_refl) in HR.
  revert HR; generalize (eq_refl (x := ∅)) as EQ; revert e e' Γ HT.
  generalize ∅ at -5 8 10 as X; intros; remember mtC as Δ eqn: EQΔ; remember nil as Ψ eqn: EQΨ.
  induction HT; subst; unfold eq_rect_r in *; simpl in *.
  - inversion HR.
  - inversion HR; subst.
    + apply val_typing_sound in HT1.
      eapply typing_expr_subst; eassumption.
    + eapply T_bind, HT2.
      now apply IHHT1 with eq_refl.
  - now eapply T_congE, IHHT with eq_refl.
  - inversion HR; subst.
    + eapply canArr in H; [| unfold t_arr; reflexivity].
      destruct H as [[e' [EQe HT]] | [e' [EQe HT]]]; inversion EQe; subst e'; clear EQe.
      eapply typing_expr_subst.
      * constructor; eassumption.
      * eapply typing_expr_subst; [| eassumption].
        apply typing_shift_val; assumption.
    + eapply canArr in H; [| unfold t_arr; reflexivity].
      destruct H as [[e' [EQe HT]] | [e' [EQe HT]]]; inversion EQe; subst e'; clear EQe.
      eapply typing_expr_subst; eassumption.
  - inversion HR; subst.
    eapply canTArr in H; [| unfold t_all; reflexivity].
    destruct H as [e [EQe HT]]; inversion EQe; subst e'; clear EQe.
    apply typing_expr_bind_types with (f := mk_subst σ) in HT.
    term_simpl in HT; eapply etypes_equiv_ctx, HT; intros [].
  - inversion HR; subst.
    eapply canProd in H; [| unfold t_prod; reflexivity].
    destruct H as [v [u [EQ [HTv HTu]]]]; inversion EQ; subst v1 v2; clear EQ.
    now apply T_val.
  - inversion HR; subst.
    eapply canProd in H; [| unfold t_prod; reflexivity].
    destruct H as [v [u [EQ [HTv HTu]]]]; inversion EQ; subst v1 v2; clear EQ.
    now apply T_val.
  - inversion HR.
  - eapply canSum in H; [| unfold t_sum; reflexivity].
    destruct H as [[v1 [EQ HTv]] | [v2 [EQ HTv]]]; subst; inversion HR; subst;
      eapply typing_expr_subst; eassumption.
  - eapply canXist in H; [| unfold t_xist; reflexivity].
    destruct H as [v' [EQ [σ HTv]]]; subst; inversion HR; subst.
    apply typing_expr_bind_types with (f := mk_subst σ) in HT; term_simpl in HT.
    eapply typing_expr_subst, etypes_equiv_ctx, HT; [exact HTv |].
    intros [| []]; reflexivity.
  - eapply canRec in H; [| reflexivity | eassumption].
    destruct H as [v' [EQ HT]]; subst; inversion HR; subst.
    now apply T_val.
  - inversion HR.
  - eapply canCArr in H0; [| reflexivity].
    destruct H0 as [e [EQ HT]]; subst; inversion HR; subst.
    apply HT, H.
  - eapply canCProd in H; [| reflexivity].
    destruct H as [v' [EQ [HTv HP]]]; subst; inversion HR; subst.
    apply (constr_cut_expr (Ψ₁ := nil) (Ψ₂ := φ :: nil) (Ψ₃ := nil)) in HT; simpl in HT.
    + eapply typing_expr_subst; eassumption.
    + simpl; now intros φ' [[] | []].
Qed.

Lemma preservation_star e e' τ (HT : mtC ∣ nil ∣ □ ⊢ₑ e : τ) (red_star : step e e')
  : mtC ∣ nil ∣ □ ⊢ₑ e' : τ.
Proof.
  induction red_star.
  - assumption.
  - apply IHred_star.
    apply preservation with x; assumption.
Qed.

(** Theorem 4.6 *)
Theorem soundness e τ (HT : mtC ∣ nil ∣ □ ⊢ₑ e : τ) :
  safe e.
Proof.
  intros e' red.
  pose proof HT as HT'.
  apply (preservation_star _ e') in HT; [| assumption].
  apply progress in HT.
  destruct HT.
  + right.
    auto.
  + left.
    auto.
Qed.
