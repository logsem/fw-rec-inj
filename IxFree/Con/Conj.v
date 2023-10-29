Require Import Utf8.
Require Import IxFree.Base.

Definition I_conj_func (P Q : IProp) : nat → Prop :=
  λ n, (n ⊨ P) ∧ (n ⊨ Q).
Lemma I_conj_func_monotone (P Q : IProp) :
  monotone (I_conj_func P Q).
Proof.
unfold monotone; unfold I_conj_func.
intros; split; apply I_valid_monotone_S; intuition.
Qed.

Definition I_conj (P Q : IProp) : IProp :=
  mk_IProp (I_conj_func P Q) (I_conj_func_monotone P Q).

Notation "A '∧ᵢ' B" := (I_conj A B) (at level 80, right associativity).

Lemma I_conj_intro {n : nat} {P Q : IProp} :
  (n ⊨ P) → (n ⊨ Q) → (n ⊨ P ∧ᵢ Q).
Proof.
intros H₁ H₂; apply I_valid_intro; split; assumption.
Qed.

Lemma I_conj_elim_M {n : nat} {P Q : IProp} :
  (n ⊨ P ∧ᵢ Q) → (n ⊨ P) ∧ (n ⊨ Q).
Proof.
intro H; apply I_valid_elim in H; apply H.
Qed.

Lemma I_conj_elim1 {n : nat} {P Q : IProp} :
  (n ⊨ P ∧ᵢ Q) → (n ⊨ P).
Proof.
intro H; apply (I_conj_elim_M H).
Qed.

Lemma I_conj_elim2 {n : nat} {P Q : IProp} :
  (n ⊨ P ∧ᵢ Q) → (n ⊨ Q).
Proof.
intro H; apply (I_conj_elim_M H).
Qed.

(* ========================================================================= *)
(* Tactics *)

Ltac isplit := apply I_conj_intro; isimplP.

Ltac idestruct_conj H H₁ H₂ :=
  apply I_conj_elim_M in H; destruct H as [ H₁ H₂ ].