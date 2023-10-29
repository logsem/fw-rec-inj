Require Import Utf8.
Require FOmegaEq.Kinds.
Require Import FOmegaEq.Types FOmegaEq.Syntax.
Require Import FOmegaEq.Universe FOmegaEq.Interp FOmegaEq.GroundView.
Require Import IxFree.Lib.
Require Import Binding.Intrinsic Binding.Lib Binding.Set.
Require Import FOmegaEq.OpSemantics.
Require Import RelationClasses Morphisms.
Require Import FOmegaEq.Presheaves.

Notation "∅" := Empty_set.
Definition vrel := IRel (value ∅ →ₛ *ₛ)%irel_sig.
Definition erel := IRel (expr ∅ →ₛ *ₛ)%irel_sig.

Module UnaryModel <: Point.
  Definition P := vrel.
End UnaryModel.

Module Export N := GView(UnaryModel).

Definition ECC (E : erel) (V : vrel) : erel :=
  λ e, (∃ᵢ v : value ∅, (e = v)ᵢ ∧ᵢ V v) ∨ᵢ (∃ᵢ e', (e ↦ e')ᵢ ∧ᵢ ▷ E e').

Lemma ECC_contr V : contractive _ (λ E, ECC E V).
Proof.
  intros R S n; iintro EQ; iintro e; isplit.
  - iintro HR; idestruct HR as HL HR; [now ileft |].
    idestruct HR as e' HR; idestruct HR as HS HR.
    iright; iexists e'; isplit; [assumption |]; later_shift.
    ispecialize EQ e'; idestruct EQ as EQ EQ'.
    now iapply EQ.
  - iintro HR; idestruct HR as HL HR; [now ileft |].
    idestruct HR as e' HR; idestruct HR as HS HR.
    iright; iexists e'; isplit; [assumption |]; later_shift.
    ispecialize EQ e'; idestruct EQ as EQ EQ'.
    now iapply EQ'.
Qed.

Definition ECL (V : vrel) : erel := I_fix _ (λ E, ECC E V) (ECC_contr V).

Lemma ECL_cons (V₁ V₂ : vrel) n (HV : n ⊨ V₁ ≾ᵢ V₂) : n ⊨ ECL V₁ ≾ᵢ ECL V₂.
Proof.
  loeb_induction; iintro e; iintro HR.
  apply (I_fix_unroll _ _ (ECC_contr V₁)) in HR; apply (I_fix_roll _ _ (ECC_contr V₂)).
  unfold ECC in *; idestruct HR as HL HR.
  - idestruct HL as v HL; idestruct HL as EQ HL; ileft; iexists v; isplit; [assumption |].
    now iapply HV.
  - idestruct HR as e' HR; idestruct HR as HS HR; iright.
    iexists e'; isplit; [assumption | later_shift; now iapply IH].
Qed.

Local Open Scope syn_scope.

(** Fig. 16. Note that this is the core of the definition, but the
    final definition is taken as a guarded fixpoint of this notion.
    This is done in RP below
*)
Fixpoint RPR (RP : gtyp → vrel) (g : gtyp) : vrel :=
  match g with
  | GAbstract P => P
  | ⊤ => λ v, (v = ⟨⟩)ᵢ
  | ⊥ => λ _, (False)ᵢ
  | g1 × g2 => λ v,
      (∃ᵢ v₁ v₂, (v = ⟨v₁, v₂⟩)ᵢ ∧ᵢ RPR RP g1 v₁ ∧ᵢ RPR RP g2 v₂)
  | g1 + g2 => λ v,
      (∃ᵢ v', (v = v_inj L v')ᵢ ∧ᵢ RPR RP g1 v') ∨ᵢ (∃ᵢ v', (v = v_inj R v')ᵢ ∧ᵢ RPR RP g2 v')
  | g1 →ᵗ g2 => λ v,
      (∀ᵢ u, RPR RP g1 u ⇒ ECL (RPR RP g2) (v u))
  | ∀ᵗ κ, φ => λ v,
      (∃ᵢ e, (v = Λ e)ᵢ ∧ᵢ
               ∀ᵢ (μ : kint κ ε),
         (sub_rel η_id μ μ)ᵢ ⇒
           ▷ ECL (RP (viewG (interpNf φ η_id ε ı%bind μ))) e)
  | ∃ᵗ κ, φ => λ v,
      (∃ᵢ v', (v = v_pack v')ᵢ ∧ᵢ ∃ᵢ (μ : kint κ ε), (sub_rel η_id μ μ)ᵢ ∧ᵢ
                                                       ▷ RP (viewG (interpNf φ η_id _ ı%bind μ)) v')
  | GRec κ φ η EQ => λ v,
      (∃ᵢ v', (v = v_roll v')ᵢ ∧ᵢ
                ▷ RP (viewG (match fkm_pkt' _ _ EQ in _ = κ return kint κ ε → kint Kinds.KTyp ε with
                             | eq_refl => applyAll (F := λ κ, kint κ ε) (List.map pkt' η)
                             end
                               (interpNf φ η_id ε ı%bind (interpNeu (neu_app (neu_ctor (Kinds.tc_rec κ)) φ) η_id)))) v')
  | χ →ᶜ g => λ v, (ctrue χ)ᵢ ⇒ ECL (RPR RP g) (e_capp v)
  | χ ×ᶜ g => λ v, ∃ᵢ v', (v = ⟨v'⟩ᶜ ∧ ctrue χ)ᵢ ∧ᵢ RPR RP g v'
  end%G.

Lemma RPR_contr : contractive (gtyp →ₛ value ∅ →ₛ *ₛ)%irel_sig RPR.
Proof.
  intros R S n; iintro EQ; iintro g; induction g; iintro v.
  - simpl; creflexivity.
  - simpl; creflexivity.
  - simpl; creflexivity.
  - simpl; isplit; iintro HR; idestruct HR as v₁ HR; idestruct HR as v₂ HR;
      idestruct HR as EQ' HR; idestruct HR as HL HR; subst.
    + iexists v₁; iexists v₂; isplit; [reflexivity | isplit].
      * ispecialize IHg1 v₁; idestruct IHg1 as HH HH'; now iapply HH.
      * ispecialize IHg2 v₂; idestruct IHg2 as HH HH'; now iapply HH.
    + iexists v₁; iexists v₂; isplit; [reflexivity | isplit].
      * ispecialize IHg1 v₁; idestruct IHg1 as HH HH'; now iapply HH'.
      * ispecialize IHg2 v₂; idestruct IHg2 as HH HH'; now iapply HH'.
  - simpl; isplit; iintro HR; idestruct HR as HR HR; idestruct HR as v' HR; idestruct HR as EQ' HR; subst.
    + ileft; iexists v'; isplit; [reflexivity |].
      ispecialize IHg1 v'; idestruct IHg1 as HH HH'; now iapply HH.
    + iright; iexists v'; isplit; [reflexivity |].
      ispecialize IHg2 v'; idestruct IHg2 as HH HH'; now iapply HH.
    + ileft; iexists v'; isplit; [reflexivity |].
      ispecialize IHg1 v'; idestruct IHg1 as HH HH'; now iapply HH'.
    + iright; iexists v'; isplit; [reflexivity |].
      ispecialize IHg2 v'; idestruct IHg2 as HH HH'; now iapply HH'.
  - simpl; isplit; iintro HR; iintro u; iintro HU.
    + iapply ECL_cons; [| iapply HR].
      * iintro w; iintro HW; ispecialize IHg2 w; idestruct IHg2 as HH HH'; now iapply HH.
      * ispecialize IHg1 u; idestruct IHg1 as HH HH'; now iapply HH'.
    + iapply ECL_cons; [| iapply HR].
      * iintro w; iintro HW; ispecialize IHg2 w; idestruct IHg2 as HH HH'; now iapply HH'.
      * ispecialize IHg1 u; idestruct IHg1 as HH HH'; now iapply HH.
  - simpl; isplit; iintro HR; idestruct HR as e HR; idestruct HR as EQ' HR; subst;
      iexists e; (isplit; [reflexivity |]); iintro μ; iintro HH; ispecialize HR μ;
      (ispecialize HR; [assumption | later_shift]).
    + iapply ECL_cons; [| exact HR].
      iintro u; ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)).
      ispecialize EQ u; now idestruct EQ as EQ1 EQ2.
    + iapply ECL_cons; [| exact HR].
      iintro u; ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)).
      ispecialize EQ u; now idestruct EQ as EQ1 EQ2.
  - simpl; isplit; iintro HR; idestruct HR as v' HR; idestruct HR as EQ' HR; subst;
      idestruct HR as μ HR; idestruct HR as HH HR; iexists v'; (isplit; [reflexivity |]);
      iexists μ; (isplit; [assumption | later_shift]).
    + ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)); ispecialize EQ v'.
      idestruct EQ as EQ1 EQ2; now iapply EQ1.
    + ispecialize EQ (viewG (interpNf n0 η_id _ ı%bind μ)); ispecialize EQ v'.
      idestruct EQ as EQ1 EQ2; now iapply EQ2.
  - simpl; isplit; iintro HR; idestruct HR as v' HR; idestruct HR as EQ' HR; subst;
      iexists v'; (isplit; [reflexivity |]); later_shift.
    + ispecialize EQ (viewG
                        (match fkm_pkt' (fkind Kinds.KTyp η) η eq_refl in (_ = κ) return kint κ ε → kint Kinds.KTyp ε with
                         | eq_refl => applyAll (F := λ κ, kint κ ε) (List.map pkt' η)
                         end
                           (interpNf μ η_id ε ı%bind (interpNeu (neu_app (neu_ctor (Kinds.tc_rec (fkind _ η))) μ) η_id))));
        ispecialize EQ v'.
      idestruct EQ as EQ1 EQ2; now iapply EQ1.
    + ispecialize EQ (viewG
                        (match fkm_pkt' (fkind Kinds.KTyp η) η eq_refl in (_ = κ) return kint κ ε → kint Kinds.KTyp ε with
                         | eq_refl => applyAll (F := λ κ, kint κ ε) (List.map pkt' η)
                         end
                           (interpNf μ η_id ε ı%bind (interpNeu (neu_app (neu_ctor (Kinds.tc_rec (fkind _ η))) μ) η_id))));
        ispecialize EQ v'.
      idestruct EQ as EQ1 EQ2; now iapply EQ2.
  - simpl; isplit; iintro HR; iintro HH.
    + iapply ECL_cons; [| now iapply HR].
      iintro u; ispecialize IHg u; now idestruct IHg as HH1 HH2.
    + iapply ECL_cons; [| now iapply HR].
      iintro u; ispecialize IHg u; now idestruct IHg as HH1 HH2.
  - simpl; isplit; iintro HR; idestruct HR as u HR; idestruct HR as HH HR; destruct HH; subst.
    + iexists u; isplit; [now split |].
      ispecialize IHg u; idestruct IHg as HH HH'; now iapply HH.
    + iexists u; isplit; [now split |].
      ispecialize IHg u; idestruct IHg as HH HH'; now iapply HH'.
Qed.

Definition RP := I_fix (gtyp →ₛ value ∅ →ₛ *ₛ)%irel_sig RPR RPR_contr.

(** Fig. 17, the logical relation. Some of the notions in the paper are inlined. *)
Definition logrelV {X : Set} (Δ : Ctx Kinds.kind) (Ψ : list (constr Δ)) (Γ : X → typ Kinds.KTyp Δ)
  (v : value X) (τ : typ Kinds.KTyp Δ) :=
  ∀ (η : NSub Δ ε) (Rη : sub_relS η_id η η) (HH : ∀ ψ, List.In ψ Ψ → ctrue (interpC ψ η)),
  ∀ (γ : X [⇒] ∅) n (HG : n ⊨ ∀ᵢ x, RP (viewG (interp (Γ x) η)) (γ x)),
  n ⊨ RP (viewG (interp τ η)) (bind γ v).

Definition logrelE {X : Set} (Δ : Ctx Kinds.kind) (Ψ : list (constr Δ)) (Γ : X → typ Kinds.KTyp Δ)
  (e : expr X) (τ : typ Kinds.KTyp Δ) :=
  ∀ (η : NSub Δ ε) (Rη : sub_relS η_id η η) (HH : ∀ ψ, List.In ψ Ψ → ctrue (interpC ψ η)),
  ∀ (γ : X [⇒] ∅) n (HG : n ⊨ ∀ᵢ x, RP (viewG (interp (Γ x) η)) (γ x)),
  n ⊨ ECL (RP (viewG (interp τ η))) (bind γ e).

Notation "Δ ∣ Ψ ∣ Γ ⊨ₑ e : τ" := (logrelE Δ Ψ%typ Γ%typ e%syn τ%typ) (at level 70, Ψ, Γ, e at level 60).
Notation "Δ ∣ Ψ ∣ Γ ⊨ᵥ v : τ" := (logrelV Δ Ψ%typ Γ%typ v%syn τ%typ) (at level 70, Ψ, Γ, v at level 60).
