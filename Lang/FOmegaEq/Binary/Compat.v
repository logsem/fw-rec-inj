Require Import Utf8.
Require Import IxFree.Lib List.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Binding.Env.

Require Import FOmegaEq.Binary.Realize FOmegaEq.Types FOmegaEq.Syntax FOmegaEq.Interp FOmegaEq.Universe.
Require Import FOmegaEq.Presheaves.
Require Import FOmegaEq.Typing.
Require FOmegaEq.Kinds.
Import Kinds.DED_kind.
Require Import Morphisms.

Lemma congV {X Δ} (Ψ : list (constr Δ)) Γ τ₁ τ₂ (v v' : value X) :
  tproves_i Ψ (c_eq _ τ₁ τ₂) → logrelV Δ Ψ Γ v v' τ₁ → logrelV Δ Ψ Γ v v' τ₂.
Proof.
  intros HP HR η HRη HT γ γ' n HΓ.
  apply tproves_int in HP.
  specialize (HP _ η HRη HT); simpl in HP; foldArrs.
  eapply reify_refl_inj in HP; [| assumption].
  unfold Presheaves.eq1 in HP; simpl in HP.
  rewrite <- HP; apply HR; assumption.
Qed.

Lemma lamC {X Δ} Ψ Γ τ χ (e e' : expr X) :
  logrelE Δ (χ :: Ψ) Γ e e' τ → logrelV Δ Ψ Γ (v_lamC e) (v_lamC e') (t_carr χ τ).
Proof.
  intros HR η HRη HT γ γ' n HΓ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP.
  simpl; iintro HTχ.
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RPR RP (viewG (interp τ η)))).
  iright; iexists (bind γ e); iexists (bind γ' e').
  isplit; [constructor | isplit; [apply OpSemantics.head_step_step; constructor | later_shift]].
  iapply ECL_cons; [| apply HR with (η := η); [assumption | | assumption]].
  - iintro u₁; iintro u₂; iintro HH; apply (I_fix_unroll _ _ RPR_contr), HH.
  - intros ψ [EQ | IN]; [now subst | auto].
Qed.

Lemma appC {X Δ} Ψ Γ τ χ (v v' : value X) :
  tproves_i Ψ χ → logrelV Δ Ψ Γ v v' (t_carr χ τ) → logrelE Δ Ψ Γ (e_capp v) (e_capp v') τ.
Proof.
  intros HP HR η HRη HT γ γ' n Hγ; term_simpl; specialize (HR η HRη HT γ γ' n Hγ).
  apply tproves_int in HP; specialize (HP _ η HRη HT); simpl in HP.
  apply (I_fix_unroll _ _ RPR_contr) in HR; fold RP in HR; simpl in HR.
  ispecialize HR; [assumption |]; term_simpl; foldArrs.
  iapply ECL_cons; [| exact HR]; iintro u₁; iintro u₂; iintro HH.
  apply (I_fix_roll _ _ RPR_contr), HH.
Qed.

Lemma tlam {X Δ} Ψ Γ κ τ (e e' : expr X) :
  logrelE (Δ ▹ κ) (map shift Ψ) (Basics.compose shift Γ) e e' τ →
  logrelV Δ Ψ Γ (v_tlam e) (v_tlam e') (t_app (t_ctor (Kinds.tc_all κ)) (t_lam τ)).
Proof.
  intros HR η HRη HT γ γ' n HΓ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ e); iexists (bind γ' e'); isplit; [reflexivity | isplit; [reflexivity |]].
  iintro μ; iintro Hμ; later_shift; foldArrs.
  change (interpNeu ( (interp τ _)) _) with (interpNf ( (reify (interp τ (nsub_ext (shift η) 0ⁱ)))) (nsub_ext (fmap ı%bind η_id) μ)).
  rewrite reinterpret_ext by assumption; apply HR.
  - intros [| x] κ' EQ; subst; simpl; [assumption | apply HRη].
  - intros ψ HIn; rewrite in_map_iff in HIn; destruct HIn as [χ [EQ HIn]]; subst.
    rewrite interpC_shift; apply HT, HIn.
  - iintro x; unfold Basics.compose.
    assert (HH := interp_shift η μ (Γ x)); red in HH; simpl in HH; rewrite HH; iapply HΓ.
Qed.

Lemma tapp {X Δ} Ψ Γ κ τ (σ : typ κ Δ) (v v' : value X) :
  logrelV Δ Ψ Γ v v' (t_app (t_ctor (Kinds.tc_all κ)) (t_lam τ)) →
  logrelE Δ Ψ Γ (e_tapp v) (e_tapp v') (subst τ σ).
Proof.
  intros HR η HRη HT γ γ' n Hγ; term_simpl.
  specialize (HR η HRη HT γ γ' n Hγ).
  apply (I_fix_unroll _ _ RPR_contr) in HR; fold RP in HR.
  simpl in HR; idestruct HR as e HR; idestruct HR as e' HR; idestruct HR as EQ HR; idestruct HR as EQ' HR; subst.
  rewrite EQ, EQ'.
  ispecialize HR (interp σ η); ispecialize HR; [apply interp_rel, HRη | foldArrs].
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp (subst τ σ) η)))).
  iright; iexists e; iexists e'.
  isplit; [constructor |].
  isplit; [apply OpSemantics.head_step_step; constructor |].
  assert (HH := interp_subst η τ σ); red in HH; simpl in HH; rewrite HH.
  rewrite <- reinterpret_ext by assumption; apply HR.
Qed.

Lemma pack {X Δ} Ψ Γ κ τ σ (v v' : value X) :
  logrelV Δ Ψ Γ v v' (subst τ σ) →
  logrelV Δ Ψ Γ (v_pack v) (v_pack v') (t_app (t_ctor (Kinds.tc_xist κ)) (t_lam τ)).
Proof.
  intros HR η HRη HT γ γ' n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ v); iexists (bind γ' v'); isplit; [reflexivity | isplit; [reflexivity |]].
  iexists (interp σ η); isplit; [apply interp_rel, HRη | foldArrs; later_shift].
  specialize (HR η HRη HT γ γ' n Hγ).
  assert (HH := interp_subst η τ σ); red in HH; simpl in HH.
  rewrite HH, <- reinterpret_ext in HR by assumption; apply HR.
Qed.

Lemma unpack {X Δ} Ψ Γ κ τ τ' (v v' : value X) (e e' : expr (inc X)) :
  logrelV Δ Ψ Γ v v' (t_app (t_ctor (Kinds.tc_xist κ)) (t_lam τ)) →
  logrelE (Δ ▹ κ) (map shift Ψ) (Env.extend (Basics.compose shift Γ) τ) e e' (shift τ') →
  logrelE Δ Ψ Γ (e_unpack v e) (e_unpack v' e') τ'.
Proof.
  intros HV HE η Hη HT γ γ' n Hγ; term_simpl.
  specialize (HV η Hη HT γ γ' n Hγ); apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV.
  simpl in HV; idestruct HV as v₁ HV; idestruct HV as v₂ HV; idestruct HV as EQ HV; idestruct HV as EQ' HV; rewrite EQ, EQ'.
  idestruct HV as μ HV; idestruct HV as Hμ HV; foldArrs.
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ' η)))).
  iright; iexists (subst (bind (γ ↑)%bind e) v₁); iexists (subst (bind (γ' ↑)%bind e') v₂); isplit; [constructor |].
  isplit; [apply OpSemantics.head_step_step; constructor |].
  unfold subst; rewrite ->2 bind_bind_comp'; later_shift.
  specialize (HE (nsub_ext η μ)); simpl in HE.
  assert (HI := interp_shift η μ τ'); red in HI; simpl in HI; rewrite HI in HE; clear HI.
  apply HE; clear HE.
  - intros [| x] κ' EQ''; subst; simpl; [apply Hμ | apply Hη].
  - intros ψ HIn; rewrite in_map_iff in HIn; destruct HIn as [χ [EQ'' HIn]]; subst.
    rewrite interpC_shift; apply HT, HIn.
  - iintro x; destruct x as [| x]; unfold Basics.compose; term_simpl.
    + rewrite <- reinterpret_ext by assumption; apply HV.
    + assert (HH := interp_shift η μ (Γ x)); red in HH; simpl in HH; rewrite HH; iapply Hγ.
Qed.

Lemma valT {X Δ} Ψ Γ τ (v v' : value X) :
  logrelV Δ Ψ Γ v v' τ → logrelE Δ Ψ Γ (e_val v) (e_val v') τ.
Proof.
  intros HV η Hη HT γ γ' n Hγ; term_simpl.
  apply (I_fix_roll _ _ (ECC_contr _)); ileft.
  iexists (bind γ v); iexists (bind γ' v'); isplit; [reflexivity | simpl].
  isplit; [do 3 constructor |].
  now apply HV.
Qed.

Lemma bindT {X Δ} Ψ Γ τ₁ τ₂ (e₁ e₁' : expr X) e₂ e₂' :
  logrelE Δ Ψ Γ e₁ e₁' τ₁ → logrelE Δ Ψ (Env.extend Γ τ₁) e₂ e₂' τ₂ → logrelE Δ Ψ Γ (e_bind e₁ e₂) (e_bind e₁' e₂') τ₂.
Proof.
  intros HE₁ HE₂ η Hη HT γ γ' n Hγ; term_simpl.
  specialize (HE₁ η Hη HT γ γ' n Hγ); term_simpl in HE₁; foldArrs.
  irevert HE₁; generalize (bind γ e₁); generalize (bind γ' e₁');
    clear e₁; clear e₁'; intros e₁; intros e₁'; irevert e₁; irevert e₁'; loeb_induction.
  iintro e₁; iintro e₁'; iintro HE₁; unfold ECL in HE₁; apply (I_fix_unroll _ _ (ECC_contr _)) in HE₁.
  fold (ECL (RP (viewG (interp τ₁ η)))) in HE₁.
  idestruct HE₁ as HV HE₁.
  - apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₂ η)))).
    iright.
    simpl in HV.
    idestruct HV as v₁ HV; idestruct HV as v₂ HV;
      idestruct HV as EQ HV; idestruct HV as HS₁ HV; subst.
    iexists (subst (Inc := inc) (bind (γ ↑)%bind e₂) v₁).
    iexists (subst (Inc := inc) (bind (γ' ↑)%bind e₂') v₂).
    isplit; [constructor |].
    isplit; [apply OpSemantics.step_arg; eassumption |].
    later_shift; unfold subst; rewrite ->2 bind_bind_comp'.
    apply HE₂; [assumption ..|].
    iintro x; destruct x as [| x]; term_simpl; [apply HV | iapply Hγ].
  - idestruct HE₁ as e₁'' HE₁; idestruct HE₁ as e₂'' HE₁;
      idestruct HE₁ as HS₁ HE₁; idestruct HE₁ as HS₂ HE₁.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₂ η)))).
    iright.
    iexists (e_bind e₁'' (bind (γ ↑)%bind e₂)).
    iexists (e_bind e₂'' (bind (γ' ↑)%bind e₂')).
    isplit; [now constructor |].
    isplit; [now apply OpSemantics.ectx_step |].
    later_shift; now iapply IH.
Qed.

Lemma congE {X Δ} (Ψ : list (constr Δ)) Γ τ₁ τ₂ (e e' : expr X) :
  tproves_i Ψ (c_eq _ τ₁ τ₂) → logrelE Δ Ψ Γ e e' τ₁ → logrelE Δ Ψ Γ e e' τ₂.
Proof.
  intros HP HR η HRη HT γ γ' n HΓ.
  apply tproves_int in HP.
  specialize (HP _ η HRη HT); simpl in HP; foldArrs.
  eapply reify_refl_inj in HP; [| assumption].
  unfold Presheaves.eq1 in HP; simpl in HP.
  rewrite <- HP; apply HR; assumption.
Qed.

Lemma cabort {X : Set} {Δ} Ψ (Γ : X → _) τ ψ :
  tproves_i Ψ ψ -> tdiscr ψ → logrelE Δ Ψ Γ e_cabort e_cabort τ.
Proof.
  intros HP HD η Hη HT γ γ' n _; term_simpl; clear γ γ'.
  apply tproves_int in HP; specialize (HP _ η Hη HT).
  eapply tdiscr_int with (η := η) in HD; contradiction.
Qed.

Lemma lwith {X Δ} Ψ Γ σ τ χ (v v' : value X) e e' :
  logrelV Δ Ψ Γ v v' (t_cprod χ σ) → logrelE Δ (χ :: Ψ) (Env.extend Γ σ) e e' τ →
  logrelE Δ Ψ Γ (e_lwith v e) (e_lwith v' e') τ.
Proof.
  intros HV HE η Hη HT γ γ' n Hγ; specialize (HV η Hη HT γ γ' n Hγ); term_simpl; simpl in *; foldArrs.
  unfold RP in HV; apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV.
  idestruct HV as v₁ HV; idestruct HV as v₂ HV; idestruct HV as EQ HV.
  destruct EQ as [-> [-> HH]].
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ η)))).
  iright; iexists (subst (bind (γ ↑)%bind e) v₁); iexists (subst (bind (γ' ↑)%bind e') v₂).
  isplit; [constructor |].
  isplit; [apply OpSemantics.head_step_step; constructor | later_shift].
  unfold subst; rewrite ->2 bind_bind_comp'; apply HE; [assumption | |].
  - intros ψ [EQ' | HIn]; [now subst | now apply HT].
  - iintro x; destruct x as [| x]; term_simpl; [| now iapply Hγ].
    now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma withC {X Δ} Ψ Γ τ χ (v v' : value X) :
  tproves_i Ψ χ → logrelV Δ Ψ Γ v v' τ → logrelV Δ Ψ Γ (v_withC v) (v_withC v') (t_cprod χ τ).
Proof.
  intros HP HV η Hη HT γ γ' n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ v); iexists (bind γ' v'); isplit; [split; [reflexivity | split; [reflexivity |]]|].
  eapply tproves_int; eassumption.
  apply (I_fix_unroll _ _ RPR_contr); fold RP; now apply HV.
Qed.

Lemma unitT {X Δ} Ψ Γ : @logrelV X Δ Ψ Γ v_unit v_unit (t_ctor Kinds.tc_unit).
Proof.
  intros η _ _ γ γ' n _; term_simpl; apply (I_fix_roll _ _ RPR_contr); simpl.
  isplit; reflexivity.
Qed.

Lemma pairT {X Δ} Ψ Γ (v₁ v₁' v₂ v₂' : value X) τ₁ τ₂ :
  logrelV Δ Ψ Γ v₁ v₁' τ₁ → logrelV Δ Ψ Γ v₂ v₂' τ₂ →
  logrelV Δ Ψ Γ (v_pair v₁ v₂) (v_pair v₁' v₂') (t_app (t_app (t_ctor Kinds.tc_prod) τ₁) τ₂).
Proof.
  intros HV₁ HV₂ η Hη HT γ γ' n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iexists (bind γ v₁); iexists (bind γ v₂); iexists (bind γ' v₁'); iexists (bind γ' v₂').
  isplit; [reflexivity | isplit; [reflexivity |]].
  isplit.
  - apply (I_fix_unroll _ _ RPR_contr); fold RP; term_simpl; foldArrs.
    rewrite map_id'; now apply HV₁.
  - apply (I_fix_unroll _ _ RPR_contr); fold RP; now apply HV₂.
Qed.

Lemma lamT {X Δ} Ψ Γ (e e' : expr (inc X)) τ₁ τ₂ :
  logrelE Δ Ψ (Env.extend Γ τ₁) e e' τ₂ →
  logrelV Δ Ψ Γ (v_lam e) (v_lam e') (t_app (t_app (t_ctor Kinds.tc_arr) τ₁) τ₂).
Proof.
  intros HE η Hη HT γ γ' n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iintro u₁; iintro u₂; iintro HU; apply (I_fix_roll _ _ (ECC_contr _));
    fold (ECL (RPR RP (viewG (interp τ₂ η)))).
  iright; iexists (subst (bind (γ ↑)%bind e) u₁);
    iexists (subst (bind (γ' ↑)%bind e') u₂).
  isplit; [constructor |].
  isplit; [apply OpSemantics.head_step_step; constructor | later_shift].
  unfold subst; rewrite ->2 bind_bind_comp'.
  iapply ECL_cons; [| apply HE; [eassumption .. |]].
  - iintro v₁; iintro v₂; iintro HR.
    now apply (I_fix_unroll _ _ RPR_contr).
  - iintro x; destruct x as [| x]; term_simpl; [| now iapply Hγ].
    term_simpl in HU; rewrite map_id' in HU; foldArrs.
    now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma injLT {X Δ} Ψ Γ (v v' : value X) τ₁ τ₂ :
  logrelV Δ Ψ Γ v v' τ₁ →
  logrelV Δ Ψ Γ (v_inj L v) (v_inj L v') (t_app (t_app (t_ctor Kinds.tc_sum) τ₁) τ₂).
Proof.
  intros HV η Hη HT γ γ' n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl; ileft; iexists (bind γ v); iexists (bind γ' v').
  isplit; [reflexivity | isplit; [reflexivity |]]; apply (I_fix_unroll _ _ RPR_contr); fold RP.
  term_simpl; foldArrs; rewrite map_id'; now apply HV.
Qed.

Lemma injRT {X Δ} Ψ Γ (v v' : value X) τ₁ τ₂ :
  logrelV Δ Ψ Γ v v' τ₂ →
  logrelV Δ Ψ Γ (v_inj R v) (v_inj R v') (t_app (t_app (t_ctor Kinds.tc_sum) τ₁) τ₂).
Proof.
  intros HV η Hη HT γ γ' n Hγ; term_simpl; foldArrs.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl; iright; iexists (bind γ v); iexists (bind γ' v').
  isplit; [reflexivity | isplit; [reflexivity |]]; apply (I_fix_unroll _ _ RPR_contr); fold RP; now apply HV.
Qed.

Lemma projLT {X Δ} Ψ Γ (v v' : value X) τ₁ τ₂ :
  logrelV Δ Ψ Γ v v' (t_app (t_app (t_ctor Kinds.tc_prod) τ₁) τ₂) →
  logrelE Δ Ψ Γ (e_proj L v) (e_proj L v') τ₁.
Proof.
  intros HV η Hη HT γ γ' n Hγ; specialize (HV η Hη HT γ γ' n Hγ); term_simpl; foldArrs.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV.
  idestruct HV as v₁ HV; idestruct HV as v₂ HV;
    idestruct HV as v₁' HV; idestruct HV as v₂' HV;
    idestruct HV as EQ HV; idestruct HV as EQ' HV;
    idestruct HV as HV₁ HV₂.
  rewrite EQ, EQ'.
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₁ η)))).
  iright; iexists (e_val v₁); iexists (e_val v₁'); isplit; [constructor | isplit; [apply OpSemantics.head_step_step; constructor | later_shift]].
  apply (I_fix_roll _ _ (ECC_contr _)); ileft.
  iexists v₁; iexists v₁'; isplit; [reflexivity | isplit; [apply Relation_Operators.rt1n_refl |]].
  foldArrs; term_simpl in HV₁; rewrite map_id' in HV₁.
  now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma projRT {X Δ} Ψ Γ (v v' : value X) τ₁ τ₂ :
  logrelV Δ Ψ Γ v v' (t_app (t_app (t_ctor Kinds.tc_prod) τ₁) τ₂) →
  logrelE Δ Ψ Γ (e_proj R v) (e_proj R v') τ₂.
Proof.
  intros HV η Hη HT γ γ' n Hγ; specialize (HV η Hη HT γ γ' n Hγ); term_simpl; foldArrs.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV.
  idestruct HV as v₁ HV; idestruct HV as v₂ HV;
    idestruct HV as v₁' HV; idestruct HV as v₂' HV;
    idestruct HV as EQ HV; idestruct HV as EQ' HV;
    idestruct HV as HV₁ HV₂.
  rewrite EQ, EQ'.
  apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ₁ η)))).
  iright; iexists (e_val v₂); iexists (e_val v₂'); isplit; [constructor | isplit; [apply OpSemantics.head_step_step; constructor | later_shift]].
  apply (I_fix_roll _ _ (ECC_contr _)); ileft.
  iexists v₂; iexists v₂'; isplit; [reflexivity | isplit; [apply Relation_Operators.rt1n_refl |]].
  foldArrs; term_simpl in HV₁; rewrite map_id' in HV₁.
  now apply (I_fix_roll _ _ RPR_contr).
Qed.

Lemma appT {X Δ} Ψ Γ (v v' u u' : value X) τ₁ τ₂ :
  logrelV Δ Ψ Γ v v' (t_app (t_app (t_ctor Kinds.tc_arr) τ₁) τ₂) →
  logrelV Δ Ψ Γ u u' τ₁ →
  logrelE Δ Ψ Γ (e_app v u) (e_app v' u') τ₂.
Proof.
  intros HV HU η Hη HT γ γ' n Hγ; specialize (HV η Hη HT γ γ' n Hγ); term_simpl; simpl in HV.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV; foldArrs.
  iapply ECL_cons; [iintro w; iintro w'; iintro HW; apply (I_fix_roll _ _ RPR_contr), HW |].
  iapply HV; term_simpl; rewrite map_id'; apply (I_fix_unroll _ _ RPR_contr); now apply HU.
Qed.

Lemma abortT {X Δ} Ψ Γ (v v' : value X) τ :
  logrelV Δ Ψ Γ v v' (t_ctor Kinds.tc_void) → logrelE Δ Ψ Γ (e_abort v) (e_abort v') τ.
Proof.
  intros HV η Hη HT γ γ' n Hγ; specialize (HV η Hη HT γ γ' n Hγ).
  apply (I_fix_unroll _ _ RPR_contr) in HV; simpl in HV.
  now apply I_valid_elim in HV.
Qed.

Lemma caseT {X Δ} Ψ Γ (v v' : value X) e₁ e₁' e₂ e₂' τ₁ τ₂ τ :
  logrelV Δ Ψ Γ v v' (t_app (t_app (t_ctor Kinds.tc_sum) τ₁) τ₂) →
  logrelE Δ Ψ (Env.extend Γ τ₁) e₁ e₁' τ → logrelE Δ Ψ (Env.extend Γ τ₂) e₂ e₂' τ →
  logrelE Δ Ψ Γ (e_case v e₁ e₂) (e_case v' e₁' e₂') τ.
Proof.
  intros HV HE₁ HE₂ η Hη HT γ γ' n Hγ; specialize (HV η Hη HT γ γ' n Hγ); simpl in HV.
  apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV; simpl in HV; foldArrs.
  term_simpl; idestruct HV as HV HV;
    idestruct HV as va HV; idestruct HV as vb HV;
    idestruct HV as EQ HV; idestruct HV as EQ' HV; rewrite EQ, EQ'.
  - term_simpl in HV; rewrite map_id' in HV; apply (I_fix_roll _ _ RPR_contr) in HV; fold RP in HV.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ η)))).
    iright; iexists (subst (bind (γ ↑)%bind e₁) va); iexists (subst (bind (γ' ↑)%bind e₁') vb);
      isplit; [constructor | isplit; [apply OpSemantics.head_step_step; constructor | later_shift]].
    unfold subst; rewrite ->2 bind_bind_comp'; apply HE₁; [assumption .. |].
    iintro x; destruct x as [| x]; term_simpl; [apply HV | iapply Hγ].
  - apply (I_fix_roll _ _ RPR_contr) in HV; fold RP in HV.
    apply (I_fix_roll _ _ (ECC_contr _)); fold (ECL (RP (viewG (interp τ η)))).
    iright; iexists (subst (bind (γ ↑)%bind e₂) va); iexists (subst (bind (γ' ↑)%bind e₂') vb);
      isplit; [constructor | isplit; [apply OpSemantics.head_step_step; constructor | later_shift]].
    unfold subst; rewrite ->2 bind_bind_comp'; apply HE₂; [assumption .. |].
    iintro x; destruct x as [| x]; term_simpl; [apply HV | iapply Hγ].
Qed.

Ltac genEQ e :=
  match goal with
  | |- context [match ?EQ with eq_refl => _ end] => generalize EQ as e
  end.

Lemma rollT {X Δ} Ψ Γ κ (τ : typ κ (Δ ▹ κ)) σ₁ σ₂ (v v' : value X) :
  rel_app κ (rec_type Δ κ τ) (subst (BindG := BindT) (Sb := Intrinsic.SubstitutableCore_ext) τ (rec_type Δ κ τ)) _ σ₁ σ₂ →
  logrelV Δ Ψ Γ v v' σ₂ → logrelV Δ Ψ Γ (v_roll v) (v_roll v') σ₁.
Proof.
  intros HR HV η Hη HT γ γ' n Hγ; term_simpl; apply (I_fix_roll _ _ RPR_contr); fold RP.
  apply baz in HR; destruct HR as [ζ [EQ [EQ₁ EQ₂]]]; subst; simpl.
  assert (HH := reflAppAll ζ (rec_type Δ _ τ) η eq_refl); red in HH; simpl in HH.
  rewrite HH; clear HH.
  specialize (HV η Hη HT γ γ' n Hγ).
  assert (HH := reflAppAll ζ (subst τ (BindG := BindT) (Sb := Intrinsic.SubstitutableCore_ext) (rec_type Δ _ τ)) η eq_refl); red in HH; simpl in HH.
  simpl in HV; rewrite HH in HV; clear HH; revert HV.
  generalize (fkm_intP ζ η (eq_refl (x := fkind Kinds.KTyp ζ))) as EQ; revert τ.
  generalize (fkind Kinds.KTyp ζ) as κ; intros; subst; simpl in *; change (NSub Δ ε) in η.
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
    genEQ EQ; revert τ EQ' HV.
    generalize (fkind Kinds.KTyp (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ))) as κ;
      intros.
    inversion EQ as [HH]; destruct HH; rewrite UIP_refl with (p := EQ); simpl; clear EQ.
    destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
    rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
    clear EQ₁ EQ₂.
    genEQ EQ; revert τ EQ' HV.
    generalize (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))) as κ; intros; destruct EQ; simpl.
    iexists (bind γ v); iexists (bind γ' v'); isplit; [reflexivity | isplit; [reflexivity | later_shift]].
    foldArrs.
    match goal with
    | HV : n ⊨ RP ?G₁ ?v ?v' |- n ⊨ RP ?G₂ ?v ?v' => assert (G₂ = G₁) as ->; [| assumption]
    end.
    f_equal.
    clear -EQ' Hη.
    apply (@applyAllI_eq _ _ _ _ (eq_sym EQ')).
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

Lemma unrollT {X Δ} Ψ Γ κ (τ : typ κ (Δ ▹ κ)) σ₁ σ₂ (v v' : value X) :
  rel_app κ (rec_type Δ κ τ) (subst (BindG := BindT) (Sb := Intrinsic.SubstitutableCore_ext) τ (rec_type Δ κ τ)) _ σ₁ σ₂ →
  logrelV Δ Ψ Γ v v' σ₁ → logrelE Δ Ψ Γ (e_unroll v) (e_unroll v') σ₂.
Proof.
  intros HR HV η Hη HT γ γ' n Hγ; term_simpl; apply (I_fix_roll _ _ (ECC_contr _)).
  fold (ECL (RP (viewG (interp σ₂ η)))).
  specialize (HV η Hη HT γ γ' n Hγ); apply (I_fix_unroll _ _ RPR_contr) in HV; fold RP in HV.
  revert HV; generalize (bind γ v) as va;
    generalize (bind γ' v') as vb;
    clear v v' γ γ' Hγ HT;
    intros v' v HV.
  apply baz in HR; destruct HR as [ζ [EQ [EQ₁ EQ₂]]]; subst; simpl.
  assert (HH := reflAppAll ζ (rec_type Δ _ τ) η eq_refl); red in HH; simpl in HH.
  simpl in HV; rewrite HH in HV; clear HH.
  assert (HH := reflAppAll ζ (subst (F := typ _) τ (rec_type Δ _ τ)) η eq_refl); red in HH; simpl in HH.
  rewrite HH; clear HH; revert HV.
  generalize (fkm_intP ζ η (eq_refl (x := fkind Kinds.KTyp ζ))) as EQ; revert τ.
  generalize (fkind Kinds.KTyp ζ) as κ; intros; subst; simpl in *; change (NSub Δ ε) in η.
  unfold interp in HV; simpl in HV; foldArrs; term_simpl in HV.
  rewrite yyy in HV.
  change (interp (subst (F := typ _) τ (rec_type _ _ τ)) η) with
    (eq_rect_r (λ κ, kint κ ε) (interp (subst (F := typ _) τ (rec_type _ _ τ)) η) eq_refl).
  revert HV; generalize (@eq_refl _ (fkind Kinds.KTyp (map (intP η) ζ))) at 3 4 as EQ'.
  generalize (fkind_map (λ κ, reify) (fkind Kinds.KTyp (map (intP η) ζ)) Kinds.KTyp (map (intP η) ζ) eq_refl) as EQ; revert τ.
  generalize (fkind Kinds.KTyp (map (intP η) ζ)) at -4 37 46 as κ; intros.
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
    clear EQ₁ EQ₂; revert HV; genEQ EQ; revert τ EQ'.
    generalize (fkind Kinds.KTyp (map (mapT (@mkArg)) (map (mapT (λ κ : Kinds.kind, reify)) (map (intP η) ζ)))) as κ; intros; destruct EQ; simpl in HV.
    idestruct HV as va HV;
      idestruct HV as vb HV;
      idestruct HV as EQ HV;
      idestruct HV as EQ'' HV; subst.
    iright; iexists (e_val va); iexists (e_val vb); isplit; [constructor | isplit; [apply OpSemantics.head_step_step; constructor | later_shift]].
    apply (I_fix_roll _ _ (ECC_contr _)); ileft.
    iexists va; iexists vb; isplit; [reflexivity | isplit; [apply Relation_Operators.rt1n_refl |]].
    foldArrs.
    match goal with
    | HV : n ⊨ RP ?G₁ ?v ?v' |- n ⊨ RP ?G₂ ?v ?v' => assert (G₂ = G₁) as ->; [| assumption]
    end.
    f_equal.
    clear -EQ' Hη.
    symmetry.
    apply (@applyAllI_eq _ _ _ _ (eq_sym EQ')).
    + destruct EQ'; simpl.
      unfold eq_rect_r; simpl.
      rewrite interp_subst.
      foldArrs.
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

Lemma recT {X Δ} Ψ Γ (e e' : expr (inc (inc X))) τ₁ τ₂ :
  logrelE Δ Ψ (Env.extend (Env.extend Γ (τ₁ →ᵗ τ₂)%typ) τ₁) e e' τ₂ → logrelV Δ Ψ Γ (rec e)%syn (rec e')%syn (τ₁ →ᵗ τ₂)%typ.
Proof.
  intros HE η Hη HT γ γ' n Hγ; term_simpl; foldArrs.
  loeb_induction.
  apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
  iintro u₁; iintro u₂; iintro HU; apply (I_fix_roll _ _ (ECC_contr _));
    fold (ECL (RPR RP (viewG (interp τ₂ η)))).
  iright.
  eapply I_exists_intro; eapply I_exists_intro; isplit; [now constructor | isplit; [econstructor 2; [constructor | constructor 1] | later_shift]].
  unfold subst; rewrite ->2 bind_bind_comp'; rewrite ->2 bind_bind_comp'.
  iapply ECL_cons; [| apply HE; [eassumption .. |]].
  - iintro v₁; iintro v₂; iintro HR; now apply (I_fix_unroll _ _ RPR_contr).
  - iintro x; destruct x as [| [| x]]; term_simpl; [| |].
    + term_simpl in HU; rewrite map_id' in HU; foldArrs.
      apply (I_fix_roll _ _ RPR_contr).
      apply HU.
    + term_simpl in HU; rewrite map_id' in HU; foldArrs.
      apply IH.
    + assert ((bind (mk_subst (rec bind ((γ ↑) ↑) e)%syn ∘ mk_subst (shift u₁))%bind (shift (shift (γ x))))
              = (γ x)) as ->.
      {
        rewrite <- bind_bind_comp'.
        term_simpl.
        reflexivity.
      }
      assert ((bind (mk_subst (rec bind ((γ' ↑) ↑) e')%syn ∘ mk_subst (shift u₂))%bind (shift (shift (γ' x))))
              = (γ' x)) as ->.
      {
        rewrite <- bind_bind_comp'.
        term_simpl.
        reflexivity.
      }
      iapply Hγ.
Qed.

Lemma fl_expr {X : Set} {Δ : Ctx Kinds.kind} {Ψ : list (constr Δ)}
  {Γ : X → typ Kinds.KTyp Δ}
  {e : expr X} {τ : typ Kinds.KTyp Δ}
  : typing_expr Δ Ψ Γ e τ -> logrelE Δ Ψ Γ e e τ
with fl_val {X : Set} {Δ : Ctx Kinds.kind} {Ψ : list (constr Δ)}
  {Γ : X → typ Kinds.KTyp Δ}
  {v : value X} {τ : typ Kinds.KTyp Δ}
  : typing_val Δ Ψ Γ v τ -> logrelV Δ Ψ Γ v v τ.
Proof.
  - induction 1.
    + now apply valT, fl_val.
    + eapply bindT; eassumption.
    + eapply congE; eassumption.
    + eapply appT; apply fl_val; eassumption.
    + apply tapp, fl_val; eassumption.
    + eapply projLT, fl_val; eassumption.
    + eapply projRT, fl_val; eassumption.
    + apply abortT, fl_val; eassumption.
    + eapply caseT; [apply fl_val; eassumption| eassumption | eassumption].
    + eapply unpack; [apply fl_val; eassumption| eassumption].
    + eapply unrollT; [eassumption | apply fl_val; eassumption].
    + eapply cabort; eassumption.
    + eapply appC; [eassumption | apply fl_val; eassumption].
    + eapply lwith; [apply fl_val; eassumption| eassumption].
  - induction 1.
    + subst; intros ? ? ? ? ? ? Hγ; iapply Hγ.
    + eapply congV; eassumption.
    + apply unitT.
    + apply lamT, fl_expr; assumption.
    + apply pairT; assumption.
    + apply injLT; assumption.
    + apply injRT; assumption.
    + apply tlam, fl_expr; assumption.
    + eapply pack; eassumption.
    + eapply rollT; eassumption.
    + apply lamC, fl_expr; assumption.
    + apply withC; assumption.
    + apply recT, fl_expr; assumption.
Qed.
