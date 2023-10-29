Require Import Utf8.
Require Import IxFree.Base.

Definition I_disj_func (P Q : IProp) : nat → Prop :=
  λ n, (n ⊨ P) ∨ (n ⊨ Q).
Lemma I_disj_func_monotone (P Q : IProp) :
  monotone (I_disj_func P Q).
Proof.
unfold monotone; unfold I_disj_func.
intros n H; destruct H; apply I_valid_monotone_S in H; auto.
Qed.

Definition I_disj (P Q : IProp) : IProp :=
  mk_IProp (I_disj_func P Q) (I_disj_func_monotone P Q).

Notation "A '∨ᵢ' B" := (I_disj A B) (at level 85, right associativity).

Lemma I_disj_introl {n : nat} {P Q : IProp} :
  n ⊨ P → n ⊨ P ∨ᵢ Q.
Proof.
intros H; apply I_valid_intro; left; assumption.
Qed.

Lemma I_disj_intror {n : nat} {P Q : IProp} :
  n ⊨ Q → n ⊨ P ∨ᵢ Q.
Proof.
intros H; apply I_valid_intro; right; assumption.
Qed.

Lemma I_disj_elim {n : nat} {P Q : IProp} :
  (n ⊨ P ∨ᵢ Q) → (n ⊨ P) ∨ (n ⊨ Q).
Proof.
intro H; apply I_valid_elim in H; destruct H; auto.
Qed.

(* ========================================================================= *)
(* Tactics *)

Ltac idestruct_disj H H1 H2 :=
  apply I_disj_elim in H;
  destruct H as [H1 | H2].

Ltac ileft :=
  apply I_disj_introl; isimplP.

Ltac iright :=
  apply I_disj_intror; isimplP.