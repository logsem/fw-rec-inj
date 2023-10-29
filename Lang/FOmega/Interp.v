Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import FOmega.Types FOmega.Syntax.
Require Import RelationClasses Basics Morphisms.

(** Propositional interpretation of System Fω (Section 3) *)

Record Setoid :=
  { carrier :> Type;
    eq      :  carrier → carrier → Prop;
    equiv   :> Equivalence eq
  }.

Definition props : Setoid :=
  {| carrier := Prop;
     eq P Q  := P ↔ Q;
     equiv   := _ |}.

Record EqArr {A B : Setoid} :=
  { arr :> A → B;
    arr_eq : ∀ a₁ a₂, eq A a₁ a₂ → eq B (arr a₁) (arr a₂) }.
Arguments EqArr A B : clear implicits.

#[export] Instance EquivS {A : Setoid} : Equivalence (eq A) := equiv A.

Program Definition arreq (A B : Setoid) : Setoid :=
  {| carrier := EqArr A B;
     eq f g := ∀ a, eq B (f a) (g a) |}.
Next Obligation.
  split.
  - intros f a; reflexivity.
  - intros f g EQ a; symmetry; apply EQ.
  - intros f g h EQ₁ EQ₂ a; etransitivity; [apply EQ₁ | apply EQ₂].
Qed.

#[export] Instance Proper_arr2 {A B} : Proper (eq (arreq A B) ==> eq A ==> eq B) arr.
Proof.
  intros f₁ f₂ EQf a₁ a₂ EQa; etransitivity; [apply EQf | apply arr_eq, EQa].
Qed.

#[export] Instance Proper_arr {A B} (f : arreq A B) : Proper (eq A ==> eq B) (arr f) :=
  (arr_eq f).

Fixpoint kint (κ : kind) : Setoid :=
  match κ with
  | ⋆ => props
  | κₐ ⇒ κᵣ => arreq (kint κₐ) (kint κᵣ)
  end.

Program Definition cint (Δ : Ctx kind) : Setoid :=
  {| carrier := ∀ x : dom Δ, kint (Δ x);
     eq η₁ η₂ := ∀ x, eq (kint (Δ x)) (η₁ x) (η₂ x) |}.
Next Obligation.
  split.
  - intros η x; reflexivity.
  - intros η₁ η₂ EQ x; symmetry; apply EQ.
  - intros η₁ η₂ η₃ EQ₁ EQ₂ x; etransitivity; [apply EQ₁ | apply EQ₂].
Qed.

Definition ηε : cint ε := λ x, match x with end.

Notation " 'λ₌' x , e " := {| arr := λ x, e; arr_eq := _ |} (at level 120, x at level 0, no associativity).
Notation " 'λ₌' x : τ , e " := {| arr := λ x : τ, e; arr_eq := _ |} (at level 120, x at level 0, no associativity).

Section Constants.
  Local Obligation Tactic := (Tactics.program_simpl; fold kint in *; try tauto).

Program Definition ctint {κ} (c : tconst κ) : kint κ :=
  match c in tconst κ return kint κ with
  | tc_unit => True
  | tc_void => False
  | tc_prod => λ₌ P, λ₌ Q, P ∧ Q
  | tc_sum  => λ₌ P, λ₌ Q, P ∨ Q
  | tc_arr  => λ₌ P, λ₌ Q, P → Q
  | tc_all  κ => λ₌ P, ∀ ν : kint κ, P ν
  | tc_xist κ => λ₌ P, ∃ ν : kint κ, P ν
  end.
Next Obligation.
  now setoid_rewrite H.
Qed.
Next Obligation.
  now setoid_rewrite H.
Qed.

End Constants.

Local Obligation Tactic := idtac.

Definition ext {Δ κ} : cint Δ → kint κ → cint (Δ ▹ κ) := maybe.

#[export] Instance Proper_maybe {Δ κ} : Proper (eq (cint Δ) ==> eq (kint κ) ==> eq (cint (Δ ▹ κ))) ext.
Proof.
  intros η₁ η₂ EQη ν₁ ν₂ EQν [| x]; now simpl.
Qed.

Fixpoint tint {Δ : Ctx kind} {κ} (τ : typ κ Δ) {struct τ} : EqArr (cint Δ) (kint κ).
Proof.
  unshelve
    refine (match τ in type _ κ return (EqArr (cint Δ) (kint κ)) with
            | @t_var _ κ x EQ => λ₌ η : cint Δ, eq_rect (Δ x) kint (η x) _ EQ
            | t_lam τ => λ₌ η : cint _, (λ₌ ν, tint _ _ τ (ext η ν)) : arreq _ _
            | t_app σ τ => λ₌ η, tint _ _ σ η (tint _ _ τ η)
            | t_const c => λ₌ _, ctint c
            end).
  - intros ν₁ ν₂ EQν; now rewrite EQν.
  - intros η₁ η₂ EQη; subst κ; simpl; apply EQη.
  - intros η₁ η₂ EQη ν; simpl; now rewrite EQη.
  - intros η₁ η₂ EQη; simpl; now rewrite EQη.
  - intros; simpl; reflexivity.
Defined.

Definition eqCK {κ₁ κ₂} (EQ : κ₁ = κ₂) : kint κ₁ → kint κ₂ → Prop :=
  match EQ with
  | eq_refl => eq _
  end.

Lemma map_eq {Δ₁ Δ₂ : Ctx kind} {κ} (δ : Δ₁ [→] Δ₂) (τ : typ κ Δ₁)
      (η₁ : cint Δ₁) (η₂ : cint Δ₂)
      (EQη : ∀ x : dom Δ₁, eqCK (arr_hom δ x) (η₂ (δ x)) (η₁ x)) :
  eq (kint κ) (tint τ η₁) (tint (fmap δ τ) η₂).
Proof.
  revert Δ₂ δ η₂ EQη; induction τ; intros; simpl.
  - subst κ; simpl; symmetry; specialize (EQη x); revert EQη.
    generalize (arr_hom δ x).
    generalize (η₁ x) as ν₁; generalize (Δ x) as κ; intros.
    subst κ; now simpl in *.
  - intros ν; apply IHτ; intros [| x]; simpl; [reflexivity | apply EQη].
  - etransitivity; [apply IHτ1, EQη | apply arr_eq, IHτ2, EQη].
  - reflexivity.
Qed.

Lemma shift_eq {Δ : Ctx kind} {κₐ κᵣ} (τ : typ κᵣ Δ) (η : cint Δ) (ν : kint κₐ) :
  eq (kint κᵣ) (tint τ η) (tint (shift τ) (ext η ν)).
Proof.
  apply map_eq; intros x; simpl; reflexivity.
Qed.

Lemma bind_eq {Δ₁ Δ₂ : Ctx kind} {κ} (ρ : Δ₁ [⇒] Δ₂) (τ : typ κ Δ₁)
      (η₁ : cint Δ₁) (η₂ : cint Δ₂)
      (EQη : ∀ x : dom Δ₁, eq (kint (Δ₁ x)) (η₁ x) (tint (ρ _ x eq_refl) η₂)) :
  eq (kint κ) (tint τ η₁) (tint (bind ρ τ) η₂).
Proof.
  revert Δ₂ ρ η₂ EQη; induction τ; intros; simpl.
  - subst κ; simpl; apply EQη.
  - intros ν; apply IHτ; intros [| x]; simpl; [reflexivity |].
    rewrite EQη; apply shift_eq.
  - etransitivity; [apply IHτ1, EQη | apply arr_eq, IHτ2, EQη].
  - reflexivity.
Qed.

Lemma subst_eq {Δ κₐ κᵣ} σ (τ : typ κᵣ (Δ ▹ κₐ)) (η : cint Δ) :
  eq (kint κᵣ) (tint τ (maybe η (tint σ η))) (tint (subst τ σ) η).
Proof.
  apply bind_eq; intros [| x]; simpl; reflexivity.
Qed.

Lemma tequiv_eq {Δ : Ctx kind} {κ} (τ₁ τ₂ : typ κ Δ) (HE : tequiv Δ κ τ₁ τ₂) (η : cint Δ) :
  eq (kint κ) (tint τ₁ η) (tint τ₂ η).
Proof.
  induction HE; simpl.
  - subst κ; rewrite UIP_refl with (p := EQ₂); simpl; reflexivity.
  - intros ν; apply IHHE.
  - now rewrite IHHE1, IHHE2.
  - reflexivity.
  - symmetry; apply IHHE.
  - etransitivity; [apply IHHE1 | apply IHHE2].
  - intros ν; simpl; apply (shift_eq τ η ν).
  - apply subst_eq.
Qed.

(** Theorem 3.1 *)
Fixpoint etypes_true {Δ : Ctx kind} {X : Set} {Γ : X → typ ⋆ Δ} e τ (η : cint Δ)
         (HΓ : ∀ x, tint (Γ x) η) (HT : etypes Δ Γ e τ) : tint τ η
with vtypes_true {Δ : Ctx kind} {X : Set} {Γ : X → typ ⋆ Δ} v τ (η : cint Δ)
                 (HΓ : ∀ x, tint (Γ x) η) (HT : vtypes Δ Γ v τ) : tint τ η.
Proof.
  - destruct HT.
    + eapply vtypes_true, HT; assumption.
    + eapply etypes_true, HT2; intros [| x]; simpl; [| apply HΓ].
      eapply etypes_true, HT1; assumption.
    + eapply vtypes_true in HT₁; [| eassumption].
      eapply HT₁, vtypes_true, HT₂; assumption.
    + eapply vtypes_true in HT; [| eassumption]; simpl in HT.
      now destruct HT.
    + eapply vtypes_true in HT; [| eassumption]; simpl in HT.
      now destruct HT.
    + eapply vtypes_true in HT; [| eassumption]; simpl in HT; contradiction.
    + eapply vtypes_true in HT1; [| eassumption]; simpl in HT1.
      destruct HT1 as [ν | ν].
      * eapply etypes_true, HT2; intros [| x]; simpl; [assumption | apply HΓ].
      * eapply etypes_true, HT3; intros [| x]; simpl; [assumption | apply HΓ].
    + rewrite <- (subst_eq (κᵣ := ⋆) (κₐ := κ)).
      eapply vtypes_true in HT; [| eassumption]; simpl in HT; apply HT.
    + eapply vtypes_true in HT₁; [| eassumption]; simpl in HT₁; destruct HT₁ as [ν HTσ].
      rewrite (shift_eq (κᵣ := ⋆) (κₐ := κ)) with (ν := ν).
      eapply etypes_true, HT; intros [| x]; simpl; [exact HTσ |].
      unfold compose; rewrite <- (shift_eq (κᵣ := ⋆)); apply HΓ.
    + eapply tequiv_eq in HE; rewrite <- HE.
      now eapply etypes_true, HT.
  - destruct HT; simpl; eauto.
    + subst τ; apply HΓ.
    + intros Hσ; eapply etypes_true, HT.
      intros [| x]; simpl; [apply Hσ | apply HΓ].
    + intros ν; eapply etypes_true, HT; intros x; simpl; unfold compose.
      rewrite <- (shift_eq (κᵣ := ⋆)); apply HΓ.
    + eapply vtypes_true in HT; [| eassumption].
      rewrite <- (subst_eq (κᵣ := ⋆) (κₐ := κ)) in HT.
      eexists; apply HT.
    + eapply tequiv_eq in HE; rewrite <- HE.
      now eapply vtypes_true, HT.
Qed.
