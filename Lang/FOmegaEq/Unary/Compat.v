Require Import Utf8.
Require Import IxFree.Lib List.
Require Import Binding.Env.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.

Require Import FOmegaEq.Unary.Realize FOmegaEq.Types FOmegaEq.Syntax FOmegaEq.Interp FOmegaEq.Universe.
Require Import FOmegaEq.Presheaves.
Require Import FOmegaEq.Typing.
Require FOmegaEq.Kinds.
Import Kinds.DED_kind.
Require Import Morphisms.

Lemma congV {X Δ} (Ψ : list (constr Δ)) Γ τ₁ τ₂ (v : value X) :
  Ψ ⊩ τ₁ ≃ τ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₁ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₂.
Proof.
  intros HP HR η HRη HT γ n HΓ.
  apply tproves_int in HP.
  specialize (HP _ η HRη HT); simpl in HP; foldArrs.
  eapply reify_refl_inj in HP; [| assumption].
  unfold Presheaves.eq1 in HP; simpl in HP.
  rewrite <- HP; apply HR; assumption.
Qed.

Lemma lamC {X Δ} Ψ Γ τ χ (e : expr X) :
  Δ ∣ χ :: Ψ ∣ Γ ⊨ₑ e : τ → Δ ∣ Ψ ∣ Γ ⊨ᵥ ƛᶜ e : χ →ᶜ τ.
Proof.
  intros HR η HRη HT γ n HΓ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP.
  simpl; iintro HTχ; foldArrs.
  apply (I_fix_roll _ _ (ECC_contr _)).
  change (view _ _ _) with (viewG (interp τ η)).
  fold (ECL (RPR RP (viewG (interp τ η)))).
  iright; iexists (bind γ e); isplit; [now constructor | later_shift].
  iapply ECL_cons; [| apply HR with (η := η); [assumption | | assumption]].
  - iintro u; iintro HH; apply (I_fix_unroll _ _ RPR_contr), HH.
  - intros ψ [EQ | IN]; [now subst | auto].
Qed.

Lemma appC {X Δ} Ψ Γ τ χ (v : value X) :
  Ψ ⊩ χ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v : χ →ᶜ τ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_capp v : τ.
Proof.
  intros HP HR η HRη HT γ n Hγ; term_simpl; specialize (HR η HRη HT γ n Hγ).
  revert HR; generalize (bind γ v); clear v γ Hγ; intros v HR; simpl in *; foldArrs.
  apply tproves_int in HP; specialize (HP _ η HRη HT); simpl in HP.
  apply (I_fix_unroll _ _ RPR_contr) in HR; fold RP in HR; simpl in HR.
  ispecialize HR; [assumption |]; term_simpl; foldArrs.
  iapply ECL_cons; [| exact HR];
    change (n ⊨ RPR RP (viewG (interp τ η)) ≾ᵢ (RP (viewG (interp τ η)))).
  iintro u; iintro HH; apply (I_fix_roll _ _ RPR_contr), HH.
Qed.

Lemma tlam {X Δ} Ψ Γ κ τ (e : expr X) :
  Δ ▹ κ ∣ map shift Ψ ∣ shift • Γ ⊨ₑ e : τ
  → Δ ∣ Ψ ∣ Γ ⊨ᵥ Λ e : ∀ᵗ κ, τ.
Proof.
  intros HR η HRη HT γ n HΓ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ e); isplit; [reflexivity |].
  iintro μ; iintro Hμ; later_shift; foldArrs.
  change (interpNeu (interp τ _) _) with
    (interpNf (reify (interp τ (nsub_ext (shift η) 0ⁱ))) (nsub_ext (fmap ı%bind η_id) μ)).
  rewrite reinterpret_ext by assumption; apply HR.
  - now apply sub_relS_ext.
  - intros ψ HIn; rewrite in_map_iff in HIn; destruct HIn as [χ [EQ HIn]]; subst.
    rewrite interpC_shift; apply HT, HIn.
  - iintro x; unfold compose.
    assert (HH := interp_shift η μ (Γ x)); red in HH; simpl in HH; rewrite HH; iapply HΓ.
Qed.

Lemma tapp {X Δ} Ψ Γ κ τ (σ : typ κ Δ) (v : value X) :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : ∀ᵗ κ, τ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_tapp v : subst τ σ.
Proof.
  intros HR η HRη HT γ n Hγ; term_simpl.
  specialize (HR η HRη HT γ n Hγ); revert HR.
  generalize (bind γ v); clear v Ψ Γ γ Hγ HT; intros v HR.
  apply (I_fix_unroll _ _ RPR_contr) in HR; fold RP in HR.
  simpl in HR; idestruct HR as e HR; idestruct HR as EQ HR; subst; foldArrs.
  ispecialize HR (interp σ η); ispecialize HR; [apply interp_rel, HRη | foldArrs].
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp (subst τ σ) η)))).
  iright; iexists e; isplit; [now constructor |].
  later_shift.
  assert (HH := interp_subst η τ σ); red in HH; simpl in HH; rewrite HH.
  rewrite <- reinterpret_ext by assumption; apply HR.
Qed.

Lemma pack {X Δ} Ψ Γ κ τ σ (v : value X) :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : subst τ σ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v_pack v : ∃ᵗ κ, τ.
Proof.
  intros HR η HRη HT γ n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; term_simpl; foldArrs.
  iexists (bind γ v); isplit; [reflexivity |].
  iexists (interp σ η); isplit; [apply interp_rel, HRη | foldArrs; later_shift].
  specialize (HR η HRη HT γ n Hγ).
  assert (HH := interp_subst η τ σ); red in HH; simpl in HH.
  rewrite HH, <- reinterpret_ext in HR by assumption; apply HR.
Qed.

Lemma unpack {X Δ} Ψ Γ κ τ τ' (v : value X) (e : expr (inc X)) :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : ∃ᵗ κ, τ
  → Δ ▹ κ ∣ map shift Ψ ∣ extend (shift • Γ) τ ⊨ₑ e : shift τ'
    → Δ ∣ Ψ ∣ Γ ⊨ₑ e_unpack v e : τ'.
Proof.
  intros HV HE η Hη HT γ n Hγ; term_simpl.
  specialize (HV η Hη HT γ n Hγ); apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV.
  simpl in HV; idestruct HV as v' HV; idestruct HV as EQ HV; rewrite EQ.
  idestruct HV as μ HV; idestruct HV as Hμ HV; foldArrs.
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ' η)))).
  iright; iexists (subst (bind (γ ↑)%bind e) v'); isplit; [now constructor |].
  unfold subst; rewrite bind_bind_comp'; later_shift.
  specialize (HE (nsub_ext η μ)); simpl in HE.
  assert (HI := interp_shift η μ τ'); red in HI; simpl in HI; rewrite HI in HE; clear HI.
  apply HE; clear HE.
  - now apply sub_relS_ext.
  - intros ψ HIn; rewrite in_map_iff in HIn; destruct HIn as [χ [EQ' HIn]]; subst.
    rewrite interpC_shift; apply HT, HIn.
  - iintro x; destruct x as [| x]; unfold compose; term_simpl.
    + rewrite <- reinterpret_ext by assumption; apply HV.
    + assert (HH := interp_shift η μ (Γ x)); red in HH; simpl in HH; rewrite HH; iapply Hγ.
Qed.

Lemma valT {X Δ} Ψ Γ τ (v : value X) :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ → Δ ∣ Ψ ∣ Γ ⊨ₑ v : τ.
Proof.
  intros HV η Hη HT γ n Hγ; term_simpl.
  apply (I_fix_roll _ _ (ECC_contr _)); ileft; iexists (bind γ v); isplit; [reflexivity |].
  now apply HV.
Qed.

Lemma bindT {X Δ} Ψ Γ τ₁ τ₂ (e₁ : expr X) e₂ :
  Δ ∣ Ψ ∣ Γ ⊨ₑ e₁ : τ₁ → Δ ∣ Ψ ∣ extend Γ τ₁ ⊨ₑ e₂ : τ₂ → Δ ∣ Ψ ∣ Γ ⊨ₑ e₁ >>= e₂ : τ₂.
Proof.
  intros HE₁ HE₂ η Hη HT γ n Hγ; term_simpl.
  specialize (HE₁ η Hη HT γ n Hγ); term_simpl in HE₁; foldArrs.
  irevert HE₁; generalize (bind γ e₁); clear e₁; intros e₁; irevert e₁; loeb_induction.
  iintro e₁; iintro HE₁; unfold ECL in HE₁; apply (I_fix_unroll _ _ (ECC_contr _)) in HE₁.
  fold (ECL (RP (viewG (interp τ₁ η)))) in HE₁.
  idestruct HE₁ as HV HE₁.
  - idestruct HV as v HV; idestruct HV as EQ HV; rewrite EQ; clear EQ.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₂ η)))).
    iright; iexists (subst (bind (γ ↑)%bind e₂) v); isplit; [now constructor |].
    later_shift; unfold subst; rewrite bind_bind_comp'; apply HE₂; [assumption .. |].
    iintro x; destruct x as [| x]; term_simpl; [apply HV | iapply Hγ].
  - idestruct HE₁ as e₁' HE₁; idestruct HE₁ as HR HE₁.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₂ η)))).
    iright; iexists (e_bind e₁' (bind (γ ↑)%bind e₂)); isplit; [now constructor |].
    later_shift; now iapply IH.
Qed.

Lemma congE {X Δ} (Ψ : list (constr Δ)) Γ τ₁ τ₂ (e : expr X) :
  Ψ ⊩ τ₁ ≃ τ₂ → Δ ∣ Ψ ∣ Γ ⊨ₑ e : τ₁ → Δ ∣ Ψ ∣ Γ ⊨ₑ e : τ₂.
Proof.
  intros HP HR η HRη HT γ n HΓ.
  apply tproves_int in HP.
  specialize (HP _ η HRη HT); simpl in HP; foldArrs.
  eapply reify_refl_inj in HP; [| assumption].
  unfold Presheaves.eq1 in HP; simpl in HP.
  rewrite <- HP; apply HR; assumption.
Qed.

Lemma cabort {X : Set} {Δ} Ψ (Γ : X → _) τ ψ :
  Ψ ⊩ ψ → ⊮ ψ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_cabort : τ.
Proof.
  intros HP HD η Hη HT γ n _; term_simpl; clear γ.
  apply tproves_int in HP; specialize (HP _ η Hη HT).
  eapply tdiscr_int with (η := η) in HD; contradiction.
Qed.

Lemma lwith {X Δ} Ψ Γ σ τ χ (v : value X) e :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : χ ×ᶜ σ → Δ ∣ χ :: Ψ ∣ extend Γ σ ⊨ₑ e : τ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_lwith v e : τ.
Proof.
  intros HV HE η Hη HT γ n Hγ; specialize (HV η Hη HT γ n Hγ); term_simpl; simpl in *; foldArrs.
  unfold RP in HV; apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV.
  idestruct HV as v' HV; idestruct HV as EQ HV; destruct EQ as [EQ HH]; rewrite EQ.
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ η)))).
  iright; iexists (subst (bind (γ ↑)%bind e) v'); isplit; [now constructor | later_shift].
  unfold subst; rewrite bind_bind_comp'; apply HE; [assumption | |].
  - intros ψ [EQ' | HIn]; [now subst | now apply HT].
  - iintro x; destruct x as [| x]; term_simpl; [| now iapply Hγ].
    now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma withC {X Δ} Ψ Γ τ χ (v : value X) :
  Ψ ⊩ χ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ → Δ ∣ Ψ ∣ Γ ⊨ᵥ ⟨v⟩ᶜ : χ ×ᶜ τ.
Proof.
  intros HP HV η Hη HT γ n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ v); isplit; [split; [reflexivity | eapply tproves_int; eassumption] |].
  apply (I_fix_unroll _ _ RPR_contr); fold RP; now apply HV.
Qed.

Lemma unitT {X : Set} {Δ} Ψ (Γ : X → typ _ Δ) : Δ ∣ Ψ ∣ Γ ⊨ᵥ ⟨⟩ : ⊤.
Proof.
  intros η _ _ γ n _; term_simpl; apply (I_fix_roll _ _ RPR_contr); simpl.
  now apply I_valid_intro.
Qed.

Lemma pairT {X Δ} Ψ Γ (v₁ v₂ : value X) τ₁ τ₂ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v₁ : τ₁ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v₂ : τ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ ⟨v₁, v₂⟩ : τ₁ × τ₂.
Proof.
  intros HV₁ HV₂ η Hη HT γ n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ v₁); iexists (bind γ v₂); isplit; [reflexivity | isplit].
  - apply (I_fix_unroll _ _ RPR_contr); fold RP; term_simpl; foldArrs.
    rewrite map_id'; now apply HV₁.
  - apply (I_fix_unroll _ _ RPR_contr); fold RP; now apply HV₂.
Qed.

Lemma lamT {X Δ} Ψ Γ (e : expr (inc X)) τ₁ τ₂ :
  Δ ∣ Ψ ∣ extend Γ τ₁ ⊨ₑ e : τ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ ƛ e : τ₁ →ᵗ τ₂.
Proof.
  intros HE η Hη HT γ n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iintro u; iintro HU; apply (I_fix_roll _ _ (ECC_contr _));
    fold (ECL (RPR RP (viewG (interp τ₂ η)))).
  iright; iexists (subst (bind (γ ↑)%bind e) u); isplit; [now constructor | later_shift].
  unfold subst; rewrite bind_bind_comp'.
  iapply ECL_cons; [| apply HE; [eassumption .. |]].
  - iintro v; iintro HR; now apply (I_fix_unroll _ _ RPR_contr).
  - iintro x; destruct x as [| x]; term_simpl; [| now iapply Hγ].
    term_simpl in HU; rewrite map_id' in HU; foldArrs.
    now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma injLT {X Δ} Ψ Γ (v : value X) τ₁ τ₂ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₁ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v_inj L v : τ₁ + τ₂.
Proof.
  intros HV η Hη HT γ n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl; ileft; iexists (bind γ v).
  isplit; [reflexivity |]; apply (I_fix_unroll _ _ RPR_contr); fold RP.
  term_simpl; foldArrs; rewrite map_id'; now apply HV.
Qed.

Lemma injRT {X Δ} Ψ Γ (v : value X) τ₁ τ₂ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v_inj R v : τ₁ + τ₂.
Proof.
  intros HV η Hη HT γ n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl; iright; iexists (bind γ v).
  isplit; [reflexivity |]; apply (I_fix_unroll _ _ RPR_contr); fold RP; now apply HV.
Qed.

Lemma projLT {X Δ} Ψ Γ (v : value X) τ₁ τ₂ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₁ × τ₂ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_proj L v : τ₁.
Proof.
  intros HV η Hη HT γ n Hγ; specialize (HV η Hη HT γ n Hγ); term_simpl; foldArrs.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV.
  idestruct HV as v₁ HV; idestruct HV as v₂ HV; idestruct HV as EQ HV; idestruct HV as HV₁ HV₂.
  rewrite EQ; apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₁ η)))).
  iright; iexists (e_val v₁); isplit; [now constructor | later_shift].
  apply (I_fix_roll _ _ (ECC_contr _)); ileft; iexists v₁; isplit; [reflexivity |].
  foldArrs; term_simpl in HV₁; rewrite map_id' in HV₁.
  now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma projRT {X Δ} Ψ Γ (v : value X) τ₁ τ₂ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₁ × τ₂ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_proj R v : τ₂.
Proof.
  intros HV η Hη HT γ n Hγ; specialize (HV η Hη HT γ n Hγ); term_simpl; foldArrs.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV.
  idestruct HV as v₁ HV; idestruct HV as v₂ HV; idestruct HV as EQ HV; idestruct HV as HV₁ HV₂.
  rewrite EQ; apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₁ η)))).
  iright; iexists (e_val v₂); isplit; [now constructor | later_shift].
  apply (I_fix_roll _ _ (ECC_contr _)); ileft; iexists v₂; isplit; [reflexivity |].
  now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma appT {X Δ} Ψ Γ (v u : value X) τ₁ τ₂ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₁ →ᵗ τ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ u : τ₁ → Δ ∣ Ψ ∣ Γ ⊨ₑ v u : τ₂.
Proof.
  intros HV HU η Hη HT γ n Hγ; specialize (HV η Hη HT γ n Hγ); term_simpl; simpl in HV.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV; foldArrs.
  iapply ECL_cons; [iintro w; iintro HW; apply (I_fix_roll _ _ RPR_contr), HW |].
  iapply HV; term_simpl; rewrite map_id'; apply (I_fix_unroll _ _ RPR_contr); now apply HU.
Qed.

Lemma abortT {X Δ} Ψ Γ (v : value X) τ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : ⊥ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_abort v : τ.
Proof.
  intros HV η Hη HT γ n Hγ; specialize (HV η Hη HT γ n Hγ).
  apply (I_fix_unroll _ _ RPR_contr) in HV; simpl in HV.
  now apply I_valid_elim in HV.
Qed.

Lemma caseT {X Δ} Ψ Γ (v : value X) e₁ e₂ τ₁ τ₂ τ :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ₁ + τ₂ →
  Δ ∣ Ψ ∣ extend Γ τ₁ ⊨ₑ e₁ : τ → Δ ∣ Ψ ∣ extend Γ τ₂ ⊨ₑ e₂ : τ →
  Δ ∣ Ψ ∣ Γ ⊨ₑ e_case v e₁ e₂ : τ.
Proof.
  intros HV HE₁ HE₂ η Hη HT γ n Hγ; specialize (HV η Hη HT γ n Hγ); simpl in HV.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV; foldArrs.
  term_simpl; idestruct HV as HV HV; idestruct HV as v' HV; idestruct HV as EQ HV; rewrite EQ.
  - term_simpl in HV; rewrite map_id' in HV; apply (I_fix_roll _ _ RPR_contr) in HV; fold RP in HV.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ η)))).
    iright; iexists (subst (bind (γ ↑)%bind e₁) v'); isplit; [now constructor | later_shift].
    unfold subst; rewrite bind_bind_comp'; apply HE₁; [assumption .. |].
    iintro x; destruct x as [| x]; term_simpl; [apply HV | iapply Hγ].
  - apply (I_fix_roll _ _ RPR_contr) in HV; fold RP in HV.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ η)))).
    iright; iexists (subst (bind (γ ↑)%bind e₂) v'); isplit; [now constructor | later_shift].
    unfold subst; rewrite bind_bind_comp'; apply HE₂; [assumption .. |].
    iintro x; destruct x as [| x]; term_simpl; [apply HV | iapply Hγ].
Qed.

Ltac genEQ e :=
  match goal with
  | |- context [match ?EQ with eq_refl => _ end] => generalize EQ as e
  end.

Lemma rollT {X Δ} Ψ Γ κ (τ : typ κ (Δ ▹ κ)) σ₁ σ₂ (v : value X) :
  rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) _ σ₁ σ₂
  → Δ ∣ Ψ ∣ Γ ⊨ᵥ v : σ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ v_roll v : σ₁.
Proof.
  intros HR HV η Hη HT γ n Hγ; term_simpl; apply (I_fix_roll _ _ RPR_contr); fold RP.
  apply baz in HR; destruct HR as [ζ [EQ [EQ₁ EQ₂]]]; subst; simpl.
  assert (HH := reflAppAll ζ (rec_type Δ _ τ) η eq_refl); red in HH; simpl in HH.
  rewrite HH; clear HH.
  specialize (HV η Hη HT γ n Hγ).
  assert (HH := reflAppAll ζ (subst τ (rec_type Δ _ τ)) η eq_refl); red in HH; simpl in HH.
  simpl in HV; rewrite HH in HV; clear HH; revert HV.
  generalize (fkm_intP ζ η (eq_refl (x := fkind Kinds.KTyp ζ))) as EQ; revert τ.
  generalize (fkind Kinds.KTyp ζ) as κ; intros; subst; simpl in *.
  unfold interp; simpl; foldArrs; term_simpl.
  rewrite yyy.
  generalize (fkind_map (λ κ, reify) (fkind Kinds.KTyp (map (intP η) ζ)) Kinds.KTyp (map (intP η) ζ) eq_refl) as EQ.
  change (interp (subst τ (rec_type _ _ τ)) η) with
    (eq_rect_r (λ κ, kint κ ε) (interp (subst τ (rec_type _ _ τ)) η) eq_refl) in HV.
  revert HV; generalize (@eq_refl _ (fkind Kinds.KTyp (map (intP η) ζ))) at 1 as EQ'.
  revert τ; generalize (fkind Kinds.KTyp (map (intP η) ζ)) at -3 13 as κ; intros.
  destruct EQ; simpl; unfold viewG.
  unshelve erewrite <- xxx.
  - rewrite app_nil_r; now apply fkind_map.
  - rewrite app_nil_r; simpl; unfold eq_ind_r; simpl.
    change (type Δ) with (λ κ, typ κ Δ).
    change (NSub Δ ε) in η; term_simpl.
    change (fkind Kinds.KTyp (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))
      with (fkind Kinds.KTyp (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ))).
    genEQ EQ; revert τ EQ' HV.
    generalize (fkind Kinds.KTyp (map (mapT (λ κ, reify)) (map (intP η) ζ))) as κ;
      intros.
    inversion EQ as [HH]; destruct HH; rewrite UIP_refl with (p := EQ); simpl; clear EQ.
    destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
    rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
    clear EQ₁ EQ₂.
    change (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ))))
      with (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))).
    genEQ EQ; revert τ EQ' HV.
    change (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))) with
      (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))).
    generalize (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))) as κ; intros; destruct EQ; simpl.
    iexists (bind γ v); isplit; [reflexivity | later_shift].
    foldArrs.
    match goal with
    | HV : n ⊨ RP ?G₁ ?v |- n ⊨ RP ?G₂ ?v => assert (G₂ = G₁) as ->; [| assumption]
    end.
    f_equal.
    clear -EQ' Hη.
    apply (applyAllI_eq _ _ _ _ (eq_sym EQ')).
    + destruct EQ'; simpl.
      unfold eq_rect_r; simpl.
      rewrite interp_subst.
      rewrite (interp_reify _ (interp τ (nsub_ext (shift η) 0ⁱ))).
      reflexivity.
      unfold interpNeu; simpl; foldArrs.
      apply interp_rel.
      apply sub_relS_ext.
      * apply reflect_rel.
        unfold interpNeu; simpl; foldArrs.
        unfold interp; simpl; foldArrs.
        do 4 f_equiv.
        rewrite interp_reify.
        reflexivity.
        apply interp_rel.
        apply sub_relS_ext.
        -- apply reflect_rel.
           unfold interpNeu; simpl; foldArrs.
           reflexivity.
        -- intros x κ EQ; simpl.
           apply subrel_fmap with (η := η_id).
           intros [].
           apply Hη.
      * intros x κ EQ; simpl.
        change (nfsub Δ ε) with (NSub Δ ε) in η; term_simpl.
        subst.
        rewrite <- (fmap_ı (η x (Δ x) eq_refl)) at 2.
        apply subrel_fmap with η_id, Hη.
        intros [].
    + symmetry in EQ'.
      clear -EQ' Hη.
      induction ζ as [| [κ μ]]; simpl; constructor.
      * exists eq_refl; unfold eq_rect_r; simpl.
        rewrite argify.
        apply interp_reify, interp_rel, Hη.
      * apply IHζ.
        simpl in EQ'.
        inversion EQ'; subst.
        reflexivity.
Qed.

Lemma unrollT {X Δ} Ψ Γ κ (τ : typ κ (Δ ▹ κ)) σ₁ σ₂ (v : value X) :
  rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) _ σ₁ σ₂
  → Δ ∣ Ψ ∣ Γ ⊨ᵥ v : σ₁ → Δ ∣ Ψ ∣ Γ ⊨ₑ e_unroll v : σ₂.
Proof.
  intros HR HV η Hη HT γ n Hγ; term_simpl; apply (I_fix_roll _ _ (ECC_contr _)).
  fold (ECL (RP (viewG (interp σ₂ η)))).
  specialize (HV η Hη HT γ n Hγ); apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV.
  revert HV; generalize (bind γ v) as v'; clear v γ Hγ HT; intros v HV.
  apply baz in HR; destruct HR as [ζ [EQ [EQ₁ EQ₂]]]; subst; simpl.
  assert (HH := reflAppAll ζ (rec_type Δ _ τ) η eq_refl); red in HH; simpl in HH.
  simpl in HV; rewrite HH in HV; clear HH.
  assert (HH := reflAppAll ζ (subst (F := typ _) τ (rec_type Δ _ τ)) η eq_refl); red in HH; simpl in HH.
  rewrite HH; clear HH; revert HV.
  generalize (fkm_intP ζ η (eq_refl (x := (fkind Kinds.KTyp ζ)))) as EQ; revert τ.
  generalize (fkind Kinds.KTyp ζ) as κ; intros; subst; simpl in *.
  unfold interp in HV; simpl in HV; foldArrs; term_simpl in HV.
  rewrite yyy in HV.
  change (interp (subst (F := typ _) τ (rec_type _ _ τ)) η) with
    (eq_rect_r (λ κ, kint κ ε) (interp (subst (F := typ _) τ (rec_type _ _ τ)) η) eq_refl).
  revert HV; generalize (@eq_refl _ (fkind Kinds.KTyp (map (intP η) ζ))) at 3 4 as EQ'.
  generalize (fkind_map (λ κ, reify) (fkind Kinds.KTyp (map (intP η) ζ)) Kinds.KTyp (map (intP η) ζ) eq_refl) as EQ; revert τ.
  generalize (fkind Kinds.KTyp (map (intP η) ζ)) at -4 38 47 as κ; intros.
  destruct EQ; simpl in *; unfold viewG in HV.
  unshelve erewrite <- xxx in HV.
  - rewrite app_nil_r; now apply fkind_map.
  - rewrite app_nil_r in HV; simpl in HV; unfold eq_ind_r in HV; simpl in HV.
    revert HV; genEQ EQ; revert τ EQ'.
    generalize (fkind Kinds.KTyp (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ))) as κ;
      intros.
    inversion EQ as [HH]; destruct HH; rewrite UIP_refl with (p := EQ) in HV; simpl in *; clear EQ.
    destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
    rewrite UIP_refl with (p := EQ₂) in HV; simpl in HV; rewrite !UIP_refl with (p := EQ₁) in HV.
    clear EQ₁ EQ₂; revert HV.
    genEQ EQ; revert τ EQ'.
    generalize (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))) as κ; intros; destruct EQ; simpl in HV.
    idestruct HV as v' HV; idestruct HV as EQv HV; subst.
    iright; iexists (e_val v'); isplit; [now constructor | later_shift].
    apply (I_fix_roll _ _ (ECC_contr _)); ileft; iexists v'; isplit; [reflexivity |].
    foldArrs.
    match goal with
    | HV : n ⊨ RP ?G₁ ?v |- n ⊨ RP ?G₂ ?v => assert (G₂ = G₁) as ->; [| assumption]
    end.
    f_equal.
    clear -EQ' Hη.
    symmetry.
    apply (@applyAllI_eq _ _ _ _ (eq_sym EQ')).
    + destruct EQ'; simpl.
      unfold eq_rect_r; simpl.
      rewrite interp_subst.
      foldArrs.
      rewrite (interp_reify _ (interp τ (nsub_ext (nfsub_map mk_shift η) 0ⁱ))).
      reflexivity.
      unfold interpNeu; simpl; foldArrs.
      apply interp_rel.
      apply sub_relS_ext.
      * apply reflect_rel.
        unfold interpNeu; simpl; foldArrs.
        unfold interp; simpl; foldArrs.
        do 4 f_equiv.
        rewrite interp_reify.
        reflexivity.
        apply interp_rel.
        apply sub_relS_ext.
        -- apply reflect_rel.
           unfold interpNeu; simpl; foldArrs.
           reflexivity.
        -- intros x κ EQ; simpl.
           apply subrel_fmap with (η := η_id).
           intros [].
           apply Hη.
      * intros x κ EQ; simpl.
        change (nfsub Δ ε) with (NSub Δ ε) in η; term_simpl.
        subst.
        rewrite <- (fmap_ı (η x (Δ x) eq_refl)) at 2.
        apply subrel_fmap with η_id, Hη.
        intros [].
    + symmetry in EQ'.
      clear -EQ' Hη.
      induction ζ as [| [κ μ]]; simpl; constructor.
      * exists eq_refl; unfold eq_rect_r; simpl.
        rewrite argify.
        apply interp_reify, interp_rel, Hη.
      * apply IHζ.
        simpl in EQ'.
        inversion EQ'; subst.
        reflexivity.
Qed.

Lemma recT {X Δ} Ψ Γ (e : expr (inc (inc X))) τ₁ τ₂ :
  Δ ∣ Ψ ∣ extend (extend Γ (τ₁ →ᵗ τ₂)) τ₁ ⊨ₑ e : τ₂ → Δ ∣ Ψ ∣ Γ ⊨ᵥ rec e : τ₁ →ᵗ τ₂.
Proof.
  intros HE η Hη HT γ n Hγ; term_simpl; foldArrs.
  loeb_induction.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iintro u; iintro HU; apply (I_fix_roll _ _ (ECC_contr _));
    fold (ECL (RPR RP (viewG (interp τ₂ η)))).
  iright.
  eapply I_exists_intro; isplit; [now constructor | later_shift].
  unfold subst; rewrite ->2 bind_bind_comp'.
  iapply ECL_cons; [| apply HE; [eassumption .. |]].
  - iintro v; iintro HR; now apply (I_fix_unroll _ _ RPR_contr).
  - iintro x; destruct x as [| [| x]]; term_simpl; [| |].
    + term_simpl in HU; rewrite map_id' in HU; foldArrs.
      apply (I_fix_roll _ _ RPR_contr).
      apply HU.
    + term_simpl in HU; rewrite map_id' in HU; foldArrs.
      apply IH.
    + assert ((bind (mk_subst (rec bind ((γ ↑) ↑) e)%syn ∘ mk_subst (shift u))%bind (shift (shift (γ x))))
              = (γ x)) as ->.
      {
        rewrite <- bind_bind_comp'.
        term_simpl.
        reflexivity.
      }
      iapply Hγ.
Qed.

(* Theorem 5.8 (fundamental lemma) *)
Lemma fl_expr {X Δ Ψ Γ τ} {e : expr X}
  (HT : Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ) :
  Δ ∣ Ψ ∣ Γ ⊨ₑ e : τ
with fl_val {X Δ Ψ Γ τ} {v : value X}
  (HT : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ) :
  Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ.
Proof.
  - destruct HT.
    + now apply valT, fl_val.
    + eapply bindT; eauto.
    + eapply congE; eauto.
    + eapply appT; eauto.
    + apply tapp; eauto.
    + eapply projLT; eauto.
    + eapply projRT; eauto.
    + apply abortT; eauto.
    + eapply caseT; eauto.
    + eapply unpack; eauto.
    + eapply unrollT; eauto.
    + eapply cabort; eassumption.
    + eapply appC; eauto.
    + eapply lwith; eauto.
  - destruct HT.
    + subst; intros ? ? ? ? ? Hγ; iapply Hγ.
    + eapply congV; eauto.
    + apply unitT.
    + apply lamT; eauto.
    + apply pairT; eauto.
    + apply injLT; eauto.
    + apply injRT; eauto.
    + apply tlam; eauto.
    + eapply pack; eauto.
    + eapply rollT; eauto.
    + apply lamC; eauto.
    + apply withC; eauto.
    + eapply recT; eauto.
Qed.
