Require Import Utf8.
Require Import IxFree.Base IxFree.Relations IxFree.Connectives.
Require Import IxFree.UnaryFixpoint.

Local Open Scope irel_sig_scope.

Fixpoint Prod (Σ : IRelSig) : Type :=
  match Σ with
  | *ₛ           => unit
  | S_Forall A F => { x : A & Prod (F x) }
  end.

Fixpoint IRel_curry (Σ : IRelSig) : IRel1 (Prod Σ) → IRel Σ :=
  match Σ return IRel1 (Prod Σ) → IRel Σ with
  | *ₛ           => λ R, R tt
  | S_Forall A F => λ R x, IRel_curry (F x) (λ y, R (existT _ x y))
  end.

Fixpoint IRel_uncurry (Σ : IRelSig) : IRel Σ → IRel1 (Prod Σ) :=
  match Σ return IRel Σ → IRel1 (Prod Σ) with
  | *ₛ           => λ R _, R
  | S_Forall A F => λ R p, IRel_uncurry (F (projT1 p)) (R (projT1 p)) (projT2 p)
  end.

Lemma IRel_uncurry_equiv (Σ : IRelSig) (R₁ R₂ : IRel Σ) :
  ⊨ R₁ ≈ᵢ R₂ ⇒ 
  I_rel_equiv (Prod Σ →ₛ *ₛ) (IRel_uncurry Σ R₁) (IRel_uncurry Σ R₂).
Proof.
induction Σ; intro n; simpl.
+ iintro; iintro; auto.
+ iintro HR; iintro p; destruct p as [ x y ]; simpl.
  specialize (H x (R₁ x) (R₂ x) n); iapply H.
  iapply HR.
Qed.

Lemma IRel_curry_equiv (Σ : IRelSig) (R₁ R₂ : IRel1 (Prod Σ)) :
  ⊨ I_rel_equiv (Prod Σ →ₛ *ₛ) R₁ R₂ ⇒ IRel_curry Σ R₁ ≈ᵢ IRel_curry Σ R₂.
Proof.
induction Σ; intro n; simpl.
+ iintro H; iapply H.
+ fold Prod.
  iintro HR; iintro x.
  specialize (H x (λ y, R₁ (existT _ x y)) (λ y, R₂ (existT _ x y)) n);
    fold Prod in H.
  iapply H; simpl; iintro y; iapply HR.
Qed.

Lemma IRel_uncurry_subrel (Σ : IRelSig) (R₁ R₂ : IRel Σ) :
  subrel (Prod Σ →ₛ *ₛ) (IRel_uncurry Σ R₁) (IRel_uncurry Σ R₂) → R₁ ≾ᵣ R₂.
Proof.
induction Σ; simpl.
+ intro H; apply H; constructor.
+ intros HR x; apply H; simpl.
  intro y; apply (HR (existT _ x y)).
Qed.

Lemma IRel_uncurry_curry_id (Σ : IRelSig) (R : IRel1 (Prod Σ)) :
  ∀ n x, (n ⊨ IRel_uncurry Σ (IRel_curry Σ R) x) <-> (n ⊨ R x).
Proof.
induction Σ; intros n x; simpl.
+ destruct x; split; auto.
+ fold Prod; destruct x as [ x y ]; simpl; apply H.
Qed.