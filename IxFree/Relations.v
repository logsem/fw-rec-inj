Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Connectives.

Local Open Scope irel_sig_scope.

Fixpoint I_rel_equiv (Σ : IRelSig) : IRel Σ → IRel Σ → IProp :=
  match Σ return IRel Σ → IRel Σ → IProp with
  | *ₛ           => λ R₁ R₂, R₁ ⇔ R₂
  | S_Forall A F => λ R₁ R₂, ∀ᵢ x, I_rel_equiv (F x) (R₁ x) (R₂ x)
  end.

Notation "R ≈ᵢ S" := (I_rel_equiv _ R S) (at level 70).

Fixpoint subrel (Σ : IRelSig) : IRel Σ → IRel Σ → Prop :=
  match Σ return IRel Σ → IRel Σ → Prop with
  | *ₛ           => λ R₁ R₂, ∀ n, (n ⊨ R₁) → (n ⊨ R₂)
  | S_Forall A F => λ R₁ R₂, ∀ x, subrel (F x) (R₁ x) (R₂ x)
  end.

Notation "R ≾ᵣ S" := (subrel _ R S) (at level 70).

Fixpoint I_rel_sub (Σ : IRelSig) : IRel Σ → IRel Σ → IProp :=
  match Σ return IRel Σ → IRel Σ → IProp with
  | *ₛ           => λ R₁ R₂, R₁ ⇒ R₂
  | S_Forall A F => λ R₁ R₂, ∀ᵢ x, I_rel_sub (F x) (R₁ x) (R₂ x)
  end.

Notation "R ≾ᵢ S" := (I_rel_sub _ R S) (at level 70).

Instance CRefl_rel_equiv (Σ : IRelSig) n :
  CReflexive (I_valid_at n) (I_rel_equiv Σ).
Proof.
  intros R; induction Σ; simpl; [creflexivity |].
  iintro x; apply H.
Qed.

Instance CSymm_rel_equiv (Σ : IRelSig) n :
  CSymmetric (I_valid_at n) (I_rel_equiv Σ).
Proof.
  intros R₁ R₂ HR; induction Σ; simpl; [csymmetry; apply HR |].
  iintro x; apply H; iapply HR.
Qed.

Instance CTrans_rel_equiv (Σ : IRelSig) n :
  CTransitive (I_valid_at n) (I_rel_equiv Σ).
Proof.
  intros x y z HR₁ HR₂; induction Σ; simpl; [cetransitivity; eassumption |].
  iintro p; eapply H; [ iapply HR₁ | iapply HR₂ ].
Qed.

Instance CRefl_rel_sub (Σ : IRelSig) n :
  CReflexive (I_valid_at n) (I_rel_sub Σ).
Proof.
  intros R; induction Σ; simpl; [creflexivity | ].
  iintro x; apply H.
Qed.

Instance CTrans_rel_sub (Σ : IRelSig) n :
  CTransitive (I_valid_at n) (I_rel_sub Σ).
Proof.
  intros x y z HR₁ HR₂; induction Σ; simpl; [cetransitivity; eassumption |].
  iintro p; eapply H; [ iapply HR₁ | iapply HR₂ ].
Qed.

Lemma subrel_sub_equiv (Σ : IRelSig) n (I₁ I₂ : IRel Σ)
      (HR : n ⊨ I₁ ≈ᵢ I₂) :
  n ⊨ I₁ ≾ᵢ I₂.
Proof.
  induction Σ; simpl in *; [now idestruct HR as HR₁ HR₂ | ].
  iintro x; apply H; iapply HR.
Qed.

Lemma equiv_subrel_symcl (Σ : IRelSig) (R₁ R₂ : IRel Σ) n
      (HS₁ : n ⊨ R₁ ≾ᵢ R₂)
      (HS₂ : n ⊨ R₂ ≾ᵢ R₁) :
  n ⊨ R₁ ≈ᵢ R₂.
Proof.
  induction Σ; [simpl in *; now isplit | ].
  iintro x; apply H; [ iapply HS₁ | iapply HS₂ ].
Qed.

Fixpoint I_Rel_const (P : IProp) (Σ : IRelSig) : IRel Σ :=
  match Σ with
  | *ₛ           => P
  | S_Forall A F => λ x, I_Rel_const P (F x)
  end.

Definition I_Rel_top (Σ : IRelSig) : IRel Σ := I_Rel_const (True)ᵢ  Σ.
Definition I_Rel_bot (Σ : IRelSig) : IRel Σ := I_Rel_const (False)ᵢ Σ.

Arguments I_Rel_top Σ /.
Arguments I_Rel_bot Σ /.

Fixpoint I_Rel_inter (Σ : IRelSig) : IRel Σ → IRel Σ → IRel Σ :=
  match Σ with
  | *ₛ           => λ R₁ R₂, R₁ ∧ᵢ R₂
  | S_Forall A F => λ R₁ R₂ x, I_Rel_inter (F x) (R₁ x) (R₂ x)
  end.

Fixpoint I_Rel_union (Σ : IRelSig) : IRel Σ → IRel Σ → IRel Σ :=
  match Σ with
  | *ₛ           => λ R₁ R₂, R₁ ∨ᵢ R₂
  | S_Forall A F => λ R₁ R₂ x, I_Rel_union (F x) (R₁ x) (R₂ x)
  end.

Fixpoint I_Rel_arrow (Σ : IRelSig) : IRel Σ → IRel Σ → IRel Σ :=
  match Σ with
  | *ₛ           => λ R₁ R₂, R₁ ⇒ R₂
  | S_Forall A F => λ R₁ R₂ x, I_Rel_arrow (F x) (R₁ x) (R₂ x)
  end.

Fixpoint I_Rel_all (Σ : IRelSig) (A : Type) : IRel (A →ₛ Σ) → IRel Σ :=
  match Σ with
  | *ₛ           => λ R, ∀ᵢ a : A, R a
  | S_Forall X F => λ R x, I_Rel_all (F x) A (λ a, R a x)
  end.

Fixpoint I_Rel_xist (Σ : IRelSig) (A : Type) : IRel (A →ₛ Σ) → IRel Σ :=
  match Σ with
  | *ₛ           => λ R, ∃ᵢ a : A, R a
  | S_Forall X F => λ R x, I_Rel_xist (F x) A (λ a, R a x)
  end.

Fixpoint IRelSig_append (Σ Δ : IRelSig) : IRelSig :=
  match Σ with
  | *ₛ           => Δ
  | S_Forall A F => ∀ₛ x : A, IRelSig_append (F x) Δ
  end.

Notation "A ++ₛ B" := (IRelSig_append A B) (at level 60).

Fixpoint I_Rel_bindA (Σ Δ : IRelSig) : IRel Σ → IRel (Σ ++ₛ Δ) → IRel Δ :=
  match Σ with
  | *ₛ           => λ P R, I_Rel_arrow Δ (I_Rel_const P Δ) R
  | S_Forall A F => λ R₁ R₂,
      I_Rel_all _ _ (λ x, I_Rel_bindA (F x) Δ (R₁ x) (R₂ x))
  end.

Fixpoint I_Rel_bindX (Σ Δ : IRelSig) : IRel Σ → IRel (Σ ++ₛ Δ) → IRel Δ :=
  match Σ with
  | *ₛ           => λ P R, I_Rel_inter Δ (I_Rel_const P Δ) R
  | S_Forall A F => λ R₁ R₂,
      I_Rel_xist _ _ (λ x, I_Rel_bindX (F x) Δ (R₁ x) (R₂ x))
  end.

Delimit Scope irel_scope with irel.

Notation "⊤ᵣ" := (I_Rel_top _) : irel_scope.
Notation "⊥ᵣ" := (I_Rel_bot _) : irel_scope.
Notation "R₁ ∪ᵣ R₂" := (I_Rel_union _ R₁ R₂) (at level 40) : irel_scope.
Notation "R₁ ∩ᵣ R₂" := (I_Rel_inter _ R₁ R₂) (at level 35) : irel_scope.
Notation "R₁ ⇒ᵣ R₂" := (I_Rel_arrow _ R₁ R₂) (at level 45, right associativity) : irel_scope.
Notation "'∀ᵣ' x .. y , P" :=
  (I_Rel_all _ _ (fun x => .. (I_Rel_all _ _ (fun y => P)) .. ))
    (at level 65, x binder, y binder, right associativity) : irel_scope.
Notation "'∃ᵣ' x .. y , P" :=
  (I_Rel_xist _ _ (fun x => .. (I_Rel_xist _ _ (fun y => P)) .. ))
    (at level 65, x binder, y binder, right associativity) : irel_scope.
Notation "R₁ ↣ₐ R₂" := (I_Rel_bindA _ _ R₁ R₂) (at level 60, right associativity) : irel_scope.
Notation "R₁ ↣ₓ R₂" := (I_Rel_bindX _ _ R₁ R₂) (at level 60, right associativity) : irel_scope.

Section Properties.
  Local Open Scope irel_scope.

  Lemma IRel_top_ub Σ (R : IRel Σ) n :
    n ⊨ R ≾ᵢ ⊤ᵣ.
  Proof.
    induction Σ; [unfold I_Rel_top; iintro; exact I |].
    iintro x; apply H.
  Qed.

  Lemma IRel_bot_lb Σ (R : IRel Σ) n :
    n ⊨ ⊥ᵣ ≾ᵢ R.
  Proof.
    induction Σ; [unfold I_Rel_bot; iintro; contradiction |].
    iintro x; apply H.
  Qed.

  Lemma IRel_sumL Σ (R₁ R₂ : IRel Σ) n :
    n ⊨ R₁ ≾ᵢ R₁ ∪ᵣ R₂.
  Proof.
    induction Σ; [iintro HR₁; ileft; assumption |].
    iintro x; apply H.
  Qed.

  Lemma IRel_sumR Σ (R₁ R₂ : IRel Σ) n :
    n ⊨ R₂ ≾ᵢ R₁ ∪ᵣ R₂.
  Proof.
    induction Σ; [iintro HR₁; iright; assumption |].
    iintro x; apply H.
  Qed.

  Lemma IRel_sumC Σ (R₁ R₂ R : IRel Σ) n
        (HR₁ : n ⊨ R₁ ≾ᵢ R)
        (HR₂ : n ⊨ R₂ ≾ᵢ R) :
    n ⊨ R₁ ∪ᵣ R₂ ≾ᵢ R.
  Proof.
    induction Σ; [iintro HR; idestruct HR as HR HR; [iapply HR₁ | iapply HR₂]; assumption |].
    iintro x; apply H; [iapply HR₁ | iapply HR₂].
  Qed.

  Lemma IRel_prodL Σ (R₁ R₂ : IRel Σ) n :
    n ⊨ R₁ ∩ᵣ R₂ ≾ᵢ R₁.
  Proof.
    induction Σ; [iintro HR; idestruct HR as HR₁ HR₂; assumption |].
    iintro x; apply H.
  Qed.

  Lemma IRel_prodR Σ (R₁ R₂ : IRel Σ) n :
    n ⊨ R₁ ∩ᵣ R₂ ≾ᵢ R₂.
  Proof.
    induction Σ; [iintro HR; idestruct HR as HR₁ HR₂; assumption |].
    iintro x; apply H.
  Qed.

  Lemma IRel_prodI Σ (R₁ R₂ R : IRel Σ) n
        (HR₁ : n ⊨ R ≾ᵢ R₁)
        (HR₂ : n ⊨ R ≾ᵢ R₂) :
    n ⊨ R ≾ᵢ R₁ ∩ᵣ R₂.
  Proof.
    induction Σ; [iintro HR; isplit; [iapply HR₁ | iapply HR₂]; assumption |].
    iintro x; apply H; [iapply HR₁ | iapply HR₂].
  Qed.

  Lemma IRel_arrI Σ (R₁ R₂ R : IRel Σ) n
        (HR : n ⊨ R ∩ᵣ R₁ ≾ᵢ R₂) :
    n ⊨ R ≾ᵢ R₁ ⇒ᵣ R₂.
  Proof.
    induction Σ; [iintro HH; iintro HR₁; iapply HR; now isplit |].
    iintro x; apply H; iapply HR.
  Qed.

  Lemma IRel_arrE Σ (R₁ R₂ R : IRel Σ) n
        (HR : n ⊨ R ≾ᵢ R₁ ⇒ᵣ R₂) :
    n ⊨ R ∩ᵣ R₁ ≾ᵢ R₂.
  Proof.
    induction Σ; [iintro HH; idestruct HH as HH₁ HH₂; now iapply HR |].
    iintro x; apply H; iapply HR.
  Qed.

End Properties.