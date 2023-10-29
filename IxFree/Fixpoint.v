Require Import Utf8.
Require Import IxFree.Base IxFree.Connectives IxFree.Relations.
Require Import IxFree.UnaryFixpoint.
Require Import IxFree.RelationCurry.
Require Import IxFree.Contractive.

Require Import Arith.

Module Private.

Local Open Scope irel_sig_scope.

Lemma contractive_curry (Σ : IRelSig) :
  ∀ (f : IRel Σ → IRel Σ), contractive Σ f → 
  contractive (Prod Σ →ₛ *ₛ) 
    (λ R, IRel_uncurry _ (f (IRel_curry _ R))).
Proof.
unfold contractive; intros f Hcon R₁ R₂ n.
iintro HR.
iapply (IRel_uncurry_equiv Σ (f (IRel_curry Σ R₁)) (f (IRel_curry Σ R₂)) n).
iapply (Hcon (IRel_curry Σ R₁) (IRel_curry Σ R₂) n).
later_shift.
iapply (IRel_curry_equiv Σ R₁ R₂ n); assumption.
Qed.

Lemma contractive_unary {A : Type} (f : IRel1 A → IRel1 A) :
  contractive (A →ₛ *ₛ) f → contractive1 f.
Proof.
unfold contractive; unfold contractive1.
intros Hcon n R₁ R₂ H x.
specialize (Hcon R₁ R₂ n); ispecialize Hcon.
+ simpl; later_down; iintro y.
  later_shift.
  apply I_iff_intro_M; intros; apply H.
  apply le_lt_n_Sm; assumption.
+ simpl in Hcon.
  apply I_iff_elim_M; iapply Hcon.
Qed.

Lemma contractive_conv (Σ : IRelSig) (f : IRel Σ → IRel Σ) :
  contractive Σ f → contractive1 (λ R, IRel_uncurry _ (f (IRel_curry _ R))).
Proof.
intros; apply contractive_unary; apply contractive_curry; assumption.
Qed.

End Private.

Definition I_fix (Σ : IRelSig) (f : IRel Σ → IRel Σ) 
    (p : contractive Σ f) : IRel Σ :=
  IRel_curry Σ (I_fix1 
    (λ R, IRel_uncurry Σ (f (IRel_curry Σ R)))
    (Private.contractive_conv Σ f p)
  ).

Lemma I_fix_unroll (Σ : IRelSig) 
    (f : IRel Σ → IRel Σ) (p : contractive Σ f) :
  I_fix Σ f p ≾ᵣ f (I_fix Σ f p).
Proof.
unfold I_fix; simpl.
apply IRel_uncurry_subrel; simpl; intros x n H.
apply (I_fix1_unroll (λ R, IRel_uncurry Σ (f (IRel_curry Σ R)))).
apply IRel_uncurry_curry_id; assumption.
Qed.

Lemma I_fix_roll (Σ : IRelSig)
    (f : IRel Σ → IRel Σ) (p : contractive Σ f) :
  f (I_fix Σ f p) ≾ᵣ I_fix Σ f p.
Proof.
unfold I_fix; simpl.
apply IRel_uncurry_subrel; simpl; intros x n H.
apply IRel_uncurry_curry_id.
apply (I_fix1_roll (λ R, IRel_uncurry Σ (f (IRel_curry Σ R)))).
assumption.
Qed.