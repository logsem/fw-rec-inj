Require Import Utf8.
Require Import IxFree.Lib.
Require Import List.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Binding.Env.

Require Import FOmegaEq.Binary.Realize FOmegaEq.Types FOmegaEq.Syntax FOmegaEq.OpSemantics FOmegaEq.Interp FOmegaEq.Universe FOmegaEq.Binary.Compat.
Require Import FOmegaEq.Presheaves.
Require Import FOmegaEq.Typing.
Require FOmegaEq.Kinds.
Import -(notations) Kinds.
Import Kinds.DED_kind.
Require Import Morphisms.

Lemma adequacy_step
  (Δ : Ctx kind) (Ψ : list (constr Δ))
  (η : NSub Δ ε) (Hη : sub_relS η_id η η)
  (HΨ : (∀ ψ : constr Δ, List.In ψ Ψ → ctrue (interpC ψ η)))
  (e₁ e₂ : expr ∅)
  : logrelE Δ Ψ Env.empty_env e₁ e₂ Kinds.tc_unit -> ∀ v, (∃ n, nsteps n e₁ (e_val v)) ->
                                                         (∃ n, nsteps n e₂ (e_val v)).
Proof.
  intros HE'.
  specialize (HE' η Hη HΨ ı%bind ı%bind).
  rewrite ->2 bind_pure' in HE'.
  assert (HE : ∀ n : nat,
            n ⊨ ECL (RP (viewG (〚 tc_unit 〛 η))) e₁ e₂).
  {
    intros n.
    apply (HE' n).
    iintro x; destruct x.
  }
  clear HE' HΨ Hη.
  unfold reflect, viewG, RP, view in HE.
  simpl in HE.
  intros v [n H].
  specialize (HE n).
  remember (e_val v) as HP.
  revert HE.
  induction H as [| n' ρ ρ' ? HS HS' IH]; intros; subst.
  - apply (I_fix_unroll _ _ (ECC_contr _)) in HE.
    idestruct HE as HV HE.
    + idestruct HV as v₁ HV;
        idestruct HV as v₂ HV;
        idestruct HV as HEQ HV;
        idestruct HV as HEQ' HV.
      subst.
      apply (I_fix_unroll _ _ RPR_contr) in HV.
      simpl in HV.
      inversion HEQ; subst.
      idestruct HV as HEQ'' HEQ'''.
      subst.
      now apply erased_steps_nsteps.
    + idestruct HE as e₁' HE;
        idestruct HE as e₂' HE;
        idestruct HE as HS₁ HE;
        idestruct HE as HS₂ HE.
      inversion HS₁.
  - apply IH; [reflexivity |].
    apply (I_fix_unroll _ _ (ECC_contr _)) in HE.
    idestruct HE as HV HE.
    + idestruct HV as v₁ HV;
        idestruct HV as v₂ HV;
        idestruct HV as HEQ HV;
        idestruct HV as HEQ' HV.
      subst.
      inversion HS.
    + idestruct HE as e₁' HE;
        idestruct HE as e₂' HE;
        idestruct HE as HS₁ HE;
        idestruct HE as HS₂ HE.
      assert (ρ' = e₁').
      { eapply head_step_det; eassumption. }
      subst.
      rewrite I_later_shift in HE.
      fold (ECL (I_fix (∀ₛ (_ : gtyp) (_ _ : value ∅), *ₛ)%irel_sig RPR RPR_contr GUnit)) in *.
      eapply ECL_step.
      apply HS₂.
      apply HE.
Qed.

Inductive pctx : Set -> Set → Type :=
| pc_empty {Y} : pctx Y Y
| pc_bindL {Y X} (r : pctx Y X) (e : expr (inc X)) : pctx Y X
| pc_bindR {Y X} (e : expr X) (r : pctx (inc Y) (inc X)) : pctx (inc Y) X
| pc_caseL {Y X} (v : value X) (r : pctx (inc Y) (inc X)) (e : expr (inc X)) : pctx (inc Y) X
| pc_caseR {Y X} (v : value X) (e : expr (inc X)) (r : pctx (inc Y) (inc X)) : pctx (inc Y) X
| pc_caseC {Y X} (r : pctxv Y X) (e₁ e₂ : expr (inc X)) : pctx Y X
| pc_unpackR {Y X} (v : value X) (r : pctx (inc Y) (inc X)) : pctx (inc Y) X
| pc_lwithR {Y X} (v : value X) (r : pctx (inc Y) (inc X)) : pctx (inc Y) X
| pc_val {Y X} (r : pctxv Y X) : pctx Y X
| pc_unpackL {Y X} (r : pctxv Y X) (v : expr (inc X)) : pctx Y X
| pc_lwithL {Y X} (r : pctxv Y X) (e : expr (inc X)) : pctx Y X
| pc_appL {Y X} (r : pctxv Y X) (v : value X) : pctx Y X
| pc_appR {Y X} (v : value X) (r : pctxv Y X)  : pctx Y X
| pc_tapp {Y X} (r : pctxv Y X) : pctx Y X
| pc_proj {Y X} (ind : ax) (r : pctxv Y X) : pctx Y X
| pc_abort {Y X} (r : pctxv Y X) : pctx Y X
| pc_unroll {Y X} (r : pctxv Y X) : pctx Y X
| pc_capp {Y X} (r : pctxv Y X) : pctx Y X
with pctxv : Set -> Set -> Type :=
| pcv_pairL {Y X} (r : pctxv Y X) (v : value X) : pctxv Y X
| pcv_pairR {Y X} (v : value X) (r : pctxv Y X) : pctxv Y X
| pcv_inj {Y X} (ind : ax) (r : pctxv Y X) : pctxv Y X
| pcv_tlam {Y X} (r : pctx Y X) : pctxv Y X
| pcv_lam {Y X} (r : pctx (inc Y) (inc X)) : pctxv (inc Y) X
| pcv_rec {Y X} (r : pctx (inc (inc Y)) (inc (inc X))) : pctxv (inc (inc Y)) X
| pcv_pack {Y X} (r : pctxv Y X) : pctxv Y X
| pcv_roll {Y X} (r : pctxv Y X) : pctxv Y X
| pcv_lamC {Y X} (r : pctx Y X) : pctxv Y X
| pcv_withC {Y X} (r : pctxv Y X) : pctxv Y X
.
Arguments pctx : clear implicits.
Arguments pctxv : clear implicits.

Declare Scope pc_scope.
Delimit Scope pc_scope with pc.

Notation "◻" := pc_empty : pc_scope.
Notation "r >>= e" := (pc_bindL r e) (at level 45, right associativity, only printing) : pc_scope.
Notation "e >>= r" := (pc_bindR e r) (at level 45, right associativity, only printing) : pc_scope.
Notation "'ƛ' e" := (pcv_lam e) (at level 60) : pc_scope.
Notation "⟨ v ⟩ᶜ" := (pcv_withC v) : pc_scope.
Notation "'π₁' r" := (pc_proj L r) (at level 60) : pc_scope.
Notation "'π₂' r" := (pc_proj R r) (at level 60) : pc_scope.
Notation "'inl' r" := (pcv_inj L r) (at level 60) : pc_scope.
Notation "'inr' r" := (pcv_inj R r) (at level 60) : pc_scope.
Notation "⟨ v₁ , v₂ ⟩" := (pcv_pairL v₁ v₂) (only printing) : pc_scope.
Notation "⟨ v₁ , v₂ ⟩" := (pcv_pairR v₁ v₂) (only printing) : pc_scope.
Notation "'Λ' e" := (pcv_tlam e) (at level 60) : pc_scope.
Notation "'ƛᶜ' e" := (pcv_lamC e) (at level 60) : pc_scope.

Local Open Scope bind_scope.
Local Open Scope pc_scope.

Fixpoint fill {X Y} (C : pctx X Y) : expr X -> expr Y
  := match C in (pctx X' Y') return (expr X' → expr Y') with
     | pc_empty => fun t => t
     | pc_bindL r e => fun t => ((fill r t) >>= e)%syn
     | pc_bindR e r => fun t => (e >>= (fill r t))%syn
     | pc_caseL v r e => fun t => e_case v (fill r t) e
     | pc_caseR v e r => fun t => e_case v e (fill r t)
     | pc_caseC r e₁ e₂ => fun t => e_case (fillV r t) e₁ e₂
     | pc_unpackR v r => fun t => e_unpack v (fill r t)
     | pc_lwithR v r => fun t => e_lwith v (fill r t)
     | pc_val r => fun t => e_val (fillV r t)
     | pc_unpackL r e => fun t => e_unpack (fillV r t) e
     | pc_lwithL r e => fun t => e_lwith (fillV r t) e
     | pc_appL r v => fun t => e_app (fillV r t) v
     | pc_appR v r => fun t => e_app v (fillV r t)
     | pc_tapp r => fun t => e_tapp (fillV r t)
     | pc_proj i r => fun t => e_proj i (fillV r t)
     | pc_abort r => fun t => e_abort (fillV r t)
     | pc_unroll r => fun t => e_unroll (fillV r t)
     | pc_capp r => fun t => e_capp (fillV r t)
     end
with fillV {X Y} (C : pctxv X Y) : expr X -> value Y
     := match C in (pctxv X' Y') return (expr X' → value Y') with
        | pcv_pairL r v => fun t => v_pair (fillV r t) v
        | pcv_pairR v r => fun t => v_pair v (fillV r t)
        | pcv_inj i r => fun t => v_inj i (fillV r t)
        | pcv_tlam r => fun t => v_tlam (fill r t)
        | pcv_lam r => fun t => v_lam (fill r t)
        | pcv_rec r => fun t => v_fix (fill r t)
        | pcv_pack r => fun t => v_pack (fillV r t)
        | pcv_roll r => fun t => v_roll (fillV r t)
        | pcv_lamC r => fun t => v_lamC (fill r t)
        | pcv_withC r => fun t => v_withC (fillV r t)
        end
.
Notation "C '⟪' e '⟫'" := (fill C e) (at level 60, only printing) : pc_scope.
Notation "C '⟪' e '⟫'" := (fillV C e) (at level 60, only printing) : pc_scope.

Inductive typing_pctx
  : forall (X Y : Set) (Δ Δ' : Ctx kind)
      (Ψ : list (constr Δ))
      (Ψ' : list (constr Δ'))
      (Γ : X → typ KTyp Δ)
      (Γ' : Y → typ KTyp Δ'), pctx X Y -> typ KTyp Δ -> typ KTyp Δ' -> Prop
  :=
| t_pc_empty {X Δ Ψ Γ τ} : typing_pctx X X Δ Δ Ψ Ψ Γ Γ pc_empty τ τ
| t_pc_bindL {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' r e}
  : typing_expr Δ' Ψ' (Env.extend Γ' τ') e τ'' ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_bindL r e) τ τ''
| t_pc_bindR {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' e r}
  : typing_expr Δ' Ψ' Γ' e τ' ->
    typing_pctx (inc X) (inc Y) Δ Δ' Ψ Ψ' Γ (Env.extend Γ' τ') r τ τ'' ->
    typing_pctx (inc X) Y Δ Δ' Ψ Ψ' Γ Γ' (pc_bindR e r) τ τ''
| t_pc_caseL {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' σ v r e}
  : typing_expr Δ' Ψ' (Env.extend Γ' σ) e τ'' ->
    typing_val Δ' Ψ' Γ' v (t_sum τ' σ) ->
    typing_pctx (inc X) (inc Y) Δ Δ' Ψ Ψ' Γ (Env.extend Γ' τ') r τ τ'' ->
    typing_pctx (inc X) Y Δ Δ' Ψ Ψ' Γ Γ' (pc_caseL v r e) τ τ''
| t_pc_caseR {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' σ v e r}
  : typing_expr Δ' Ψ' (Env.extend Γ' σ) e τ'' ->
    typing_val Δ' Ψ' Γ' v (t_sum σ τ') ->
    typing_pctx (inc X) (inc Y) Δ Δ' Ψ Ψ' Γ (Env.extend Γ' τ') r τ τ'' ->
    typing_pctx (inc X) Y Δ Δ' Ψ Ψ' Γ Γ' (pc_caseR v e r) τ τ''
| t_pc_caseC {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ σ' r e₁ e₂}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_sum σ σ') ->
    typing_expr Δ' Ψ' (Env.extend Γ' σ) e₁ τ' ->
    typing_expr Δ' Ψ' (Env.extend Γ' σ') e₂ τ' ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_caseC r e₁ e₂) τ τ'
| t_pc_unpackR {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' κ σ v r}
  : typing_val Δ' Ψ' Γ' v (t_xist κ σ) ->
    typing_pctx (inc X) (inc Y) Δ (Δ' ▹ κ) Ψ (map shift Ψ') Γ
      (Env.extend (Env.compose shift Γ') σ) r τ (shift τ') ->
    typing_pctx (inc X) Y Δ Δ' Ψ Ψ' Γ Γ' (pc_unpackR v r) τ τ'
| t_pc_unpackL {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' κ σ v r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_xist κ σ) ->
    typing_expr (Δ' ▹ κ) (map shift Ψ') (Env.extend (Env.compose shift Γ') σ) v (shift τ') ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_unpackL r v) τ τ'
| t_pc_lwithR {X Y Δ Δ' Ψ Ψ' Γ Γ' φ σ τ τ' v r}
  : typing_val Δ' Ψ' Γ' v (t_cprod φ σ) ->
    typing_pctx (inc X) (inc Y) Δ Δ' Ψ (φ :: Ψ') Γ (Env.extend Γ' σ) r τ τ' ->
    typing_pctx (inc X) Y Δ Δ' Ψ Ψ' Γ Γ' (pc_lwithR v r) τ τ'
| t_pc_lwithL {X Y Δ Δ' Ψ Ψ' Γ Γ' φ σ τ τ' v r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_cprod φ σ) ->
    typing_expr Δ' (φ :: Ψ') (Env.extend Γ' σ) v τ' ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_lwithL r v) τ τ'
| t_pc_appL {X Y Δ Δ' Ψ Ψ' Γ Γ' σ τ τ' v r}
  : typing_val Δ' Ψ' Γ' v τ ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r σ (t_arr τ τ') ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_appL r v) σ τ'
| t_pc_appR {X Y Δ Δ' Ψ Ψ' Γ Γ' σ τ τ' v r}
  : typing_val Δ' Ψ' Γ' v (t_arr τ τ') ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r σ τ ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_appR v r) σ τ'
| t_pc_val {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_val r) τ τ'
| t_pc_projL {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_prod τ' τ'') ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_proj L r) τ τ'
| t_pc_projR {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_prod τ' τ'') ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_proj R r) τ τ''
| t_pc_abort {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ tc_void ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_abort r) τ τ'
| t_pc_tapp {X Y Δ Δ' Ψ Ψ' Γ Γ' τ κ τ' σ r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_all κ τ') ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_tapp r) τ (subst τ' σ)
| t_pc_capp {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' φ r}
  : Ψ' ⊩ φ ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (t_carr φ τ') ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_capp r) τ τ'
| t_pc_unroll {X Y Δ Δ' Ψ Ψ' Γ Γ' κ τ τ' σ1 σ2 r}
    {HF : rel_app κ (rec_type Δ' κ τ) (subst τ (rec_type Δ' κ τ)) KTyp σ1 σ2}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ' σ1 ->
    typing_pctx X Y Δ Δ' Ψ Ψ' Γ Γ' (pc_unroll r) τ' σ2
with typing_pctxv
       : forall (X Y : Set) (Δ Δ' : Ctx kind)
           (Ψ : list (constr Δ))
           (Ψ' : list (constr Δ'))
      (Γ : X → typ KTyp Δ)
      (Γ' : Y → typ KTyp Δ'), pctxv X Y -> typ KTyp Δ -> typ KTyp Δ' -> Prop :=
| t_pc_pairL {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' r v}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    typing_val Δ' Ψ' Γ' v τ'' ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_pairL r v) τ (t_prod τ' τ'')
| t_pc_pairR {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' τ'' r v}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    typing_val Δ' Ψ' Γ' v τ'' ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_pairR v r) τ (t_prod τ'' τ')
| t_pc_injL {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_inj L r) τ (t_sum τ' σ)
| t_pc_injR {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_inj R r) τ (t_sum σ τ')
| t_pc_lam {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ r}
  : typing_pctx (inc X) (inc Y) Δ Δ' Ψ Ψ' Γ (Env.extend Γ' σ) r τ τ' ->
    typing_pctxv (inc X) Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_lam r) τ (t_arr σ τ')
| t_pc_rec {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ r}
  : typing_pctx (inc (inc X)) (inc (inc Y)) Δ Δ' Ψ Ψ' Γ (Env.extend (Env.extend Γ' (t_arr σ τ')) σ) r τ τ' ->
    typing_pctxv (inc (inc X)) Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_rec r) τ (t_arr σ τ')
| t_pc_withC {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ τ' ->
    Ψ' ⊩ σ ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_withC r) τ (t_cprod σ τ')
| t_pc_lamC {X Y Δ Δ' Ψ Ψ' Γ Γ' τ τ' σ r}
  : typing_pctx X Y Δ Δ' Ψ (σ :: Ψ') Γ Γ' r τ τ' ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_lamC r) τ (t_carr σ τ')
| t_pc_tlam {X Y Δ Δ' Ψ Ψ' Γ Γ' τ κ τ' r}
  : typing_pctx X Y Δ (extC κ Δ') Ψ (map shift Ψ') Γ (Env.compose shift Γ') r τ τ' ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_tlam r) τ (t_all κ τ')
| t_pc_pack {X Y Δ Δ' Ψ Ψ' Γ Γ' τ κ τ' τ'' r}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ (subst τ' τ'') ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_pack r) τ (t_xist κ τ')
| t_pc_roll {X Y Δ Δ' Ψ Ψ' Γ Γ' κ τ τ' σ1 σ2 r}
    {HF : rel_app κ (rec_type Δ' κ τ) (subst τ (rec_type Δ' κ τ)) KTyp σ1 σ2}
  : typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' r τ' σ2 ->
    typing_pctxv X Y Δ Δ' Ψ Ψ' Γ Γ' (pcv_roll r) τ' σ1
.
Arguments typing_pctx {_} {_}.
Arguments typing_pctxv {_} {_}.
Notation "Δ '|' Ψ '|' Γ ';' τ '⤚' r '⇾' Δ' '|' Ψ' '|' Γ' ';' τ'" := (typing_pctx Δ Δ' Ψ Ψ' Γ Γ' r τ τ') (at level 45, right associativity, only printing) : pc_scope.
Notation "Δ '|' Ψ '|' Γ ';' τ '⤚' r '⇾' Δ' '|' Ψ' '|' Γ' ';' τ'" := (typing_pctxv Δ Δ' Ψ Ψ' Γ Γ' r τ τ') (at level 45, right associativity, only printing) : pc_scope.

Lemma logrelCongFill {X Y : Set}
  (Δ Δ' : Ctx kind)
  (Ψ : list (constr Δ))
  (Ψ' : list (constr Δ'))
  (Γ : X → typ KTyp Δ)
  (Γ' : Y → typ KTyp Δ')
  (e₁ e₂ : expr X) K (τ : typ KTyp Δ) (τ' : typ KTyp Δ')
  (HK : typing_pctx Δ Δ' Ψ Ψ' Γ Γ' K τ τ')
  : logrelE Δ Ψ Γ e₁ e₂ τ -> logrelE Δ' Ψ' Γ' (fill K e₁) (fill K e₂) τ'
with logrelCongFillV {X Y : Set}
  (Δ Δ' : Ctx kind)
  (Ψ : list (constr Δ))
  (Ψ' : list (constr Δ'))
  (Γ : X → typ KTyp Δ)
  (Γ' : Y → typ KTyp Δ')
  (e₁ e₂ : expr X) K (τ : typ KTyp Δ) (τ' : typ KTyp Δ')
  (HK : typing_pctxv Δ Δ' Ψ Ψ' Γ Γ' K τ τ')
  : logrelE Δ Ψ Γ e₁ e₂ τ -> logrelV Δ' Ψ' Γ' (fillV K e₁) (fillV K e₂) τ'.
Proof.
  {
    induction HK; subst; simpl; intros G.
    - apply G.
    - eapply bindT.
      + eapply IHHK; eassumption.
      + apply fl_expr; eassumption.
    - eapply bindT.
      + apply fl_expr; eassumption.
      + eapply IHHK; eassumption.
    - eapply caseT.
      + apply fl_val; eassumption.
      + now apply IHHK.
      + apply fl_expr; eassumption.
    - eapply caseT.
      + apply fl_val; eassumption.
      + apply fl_expr; eassumption.
      + now apply IHHK.
    - eapply caseT.
      + eapply logrelCongFillV; eassumption.
      + apply fl_expr; eassumption.
      + apply fl_expr; eassumption.
    - eapply unpack.
      + apply fl_val; eassumption.
      + apply IHHK; assumption.
    - eapply unpack.
      + eapply logrelCongFillV; eassumption.
      + apply fl_expr; eassumption.
    - eapply lwith.
      + apply fl_val; eassumption.
      + apply IHHK; assumption.
    - eapply lwith.
      + eapply logrelCongFillV; eassumption.
      + apply fl_expr; eassumption.
    - eapply appT.
      + eapply logrelCongFillV; eassumption.
      + apply fl_val; eassumption.
    - eapply appT.
      + apply fl_val; eassumption.
      + eapply logrelCongFillV; eassumption.
    - apply valT.
      eapply logrelCongFillV; eassumption.
    - eapply projLT.
      eapply logrelCongFillV; eassumption.
    - eapply projRT.
      eapply logrelCongFillV; eassumption.
    - apply abortT.
      eapply logrelCongFillV; eassumption.
    - apply tapp.
      eapply logrelCongFillV; eassumption.
    - eapply appC.
      + apply H.
      + eapply logrelCongFillV; eassumption.
    - eapply unrollT.
      apply HF.
      eapply logrelCongFillV; eassumption.
  }
  {
    induction HK; subst; simpl; intros G.
    - apply pairT.
      + apply IHHK; assumption.
      + apply fl_val; assumption.
    - apply pairT.
      + apply fl_val; assumption.
      + apply IHHK; assumption.
    - apply injLT.
      apply IHHK; assumption.
    - apply injRT.
      apply IHHK; assumption.
    - apply lamT.
      eapply logrelCongFill; eassumption.
    - apply recT.
      eapply logrelCongFill; eassumption.
    - apply withC; [eassumption |].
      eapply logrelCongFillV; eassumption.
    - apply lamC.
      eapply logrelCongFill; eassumption.
    - apply tlam.
      eapply logrelCongFill; eassumption.
    - eapply pack.
      eapply logrelCongFillV; eassumption.
    - eapply rollT.
      + apply HF.
      + eapply logrelCongFillV; eassumption.
  }
Qed.

Definition ctx_approx {X : Set}
  (Δ : Ctx kind)
  (Ψ : list (constr Δ))
  (Γ : X → typ KTyp Δ)
  (e₁ e₂ : expr X) (τ : typ KTyp Δ) :=
  ∀ {K : pctx X ∅} (HK : typing_pctx Δ mtC Ψ nil Γ Env.empty_env K τ (t_ctor tc_unit)),
  ∀ (v : value ∅), (∃ n, nsteps n (fill K e₁) (e_val v)) ->
                   (∃ n, nsteps n (fill K e₂) (e_val v)).

Lemma adequacy {X : Set}
  (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : X → typ KTyp Δ)
  (e₁ e₂ : expr X) (τ : typ KTyp Δ)
  : logrelE Δ Ψ Γ e₁ e₂ τ -> ctx_approx Δ Ψ Γ e₁ e₂ τ.
Proof.
  intros HE K HK.
  revert e₁ e₂ HE.
  intros ? ? ? ? H.
  eapply (@adequacy_step ε nil η_id).
  intros [].
  intros ? [].
  eapply (logrelCongFill _ mtC _ nil _ Env.empty_env e₁ _ (K) τ ⊤%typ); [ apply HK| apply HE].
  apply H.
Qed.
