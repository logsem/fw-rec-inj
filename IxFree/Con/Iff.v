Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Con.Arrow IxFree.Con.Conj.
Require RelationClasses.

Definition I_iff (P Q : IProp) := (P ⇒ Q) ∧ᵢ (Q ⇒ P).

Notation "A ⇔ B" := (I_iff A B) (at level 95).

Lemma I_iff_intro_M {n : nat} {P Q : IProp} :
  (∀ k, k ≤ n → ((k ⊨ P) <-> (k ⊨ Q))) → (n ⊨ P ⇔ Q).
Proof.
intro H; apply I_conj_intro; apply I_arrow_intro; apply H.
Qed.

Lemma I_iff_elim_M {n : nat} {P Q : IProp} :
  (n ⊨ P ⇔ Q) → ((n ⊨ P) <-> (n ⊨ Q)).
Proof.
intro H; split; intro H'.
+ apply I_conj_elim1 in H; apply (I_arrow_elim H H').
+ apply I_conj_elim2 in H; apply (I_arrow_elim H H').
Qed.

Lemma I_iff_refl {n : nat} {P : IProp} :
  n ⊨ P ⇔ P.
Proof.
  apply I_iff_intro_M; intros; reflexivity.
Qed.

Lemma I_iff_symm {n : nat} {P Q : IProp} (HI : n ⊨ P ⇔ Q) :
  n ⊨ Q ⇔ P.
Proof.
  apply I_iff_intro_M; intros k HLe.
  eapply I_valid_monotone, I_iff_elim_M in HI; [| eassumption].
  symmetry; assumption.
Qed.

Lemma I_iff_trans {n : nat} {P Q R : IProp}
      (HPQ : n ⊨ P ⇔ Q)
      (HQR : n ⊨ Q ⇔ R) :
  n ⊨ P ⇔ R.
Proof.
  apply I_iff_intro_M; intros k HLe.
  eapply I_valid_monotone, I_iff_elim_M in HPQ; [| eassumption].
  eapply I_valid_monotone, I_iff_elim_M in HQR; [| eassumption].
  etransitivity; eassumption.
Qed.

Instance CRefl_Iiff n : CReflexive (I_valid_at n) I_iff.
Proof.
  intros x; apply I_iff_intro_M; intros; reflexivity.
Qed.

Instance CSymm_Iiff n : CSymmetric (I_valid_at n) I_iff.
Proof.
  intros x y HR; apply I_iff_intro_M; intros; symmetry.
  now apply I_iff_elim_M, I_valid_monotone with n.
Qed.

Instance CTrans_Iiff n : CTransitive (I_valid_at n) I_iff.
Proof.
  intros x y z HR₁ HR₂; apply I_iff_intro_M; intros.
  etransitivity; eapply I_iff_elim_M, I_valid_monotone; eassumption.
Qed.
