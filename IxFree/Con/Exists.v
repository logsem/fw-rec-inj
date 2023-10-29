Require Import Utf8.
Require Import IxFree.Base.

Definition I_exists_func (A : Type) (P : A → IProp) : nat → Prop :=
  λ n, ∃ x : A, n ⊨ P x.
Lemma I_exists_func_monotone (A : Type) (P : A → IProp) :
  monotone (I_exists_func A P).
Proof.
intros n H₁; destruct H₁ as [x H₁]; exists x.
apply I_valid_monotone_S; assumption.
Qed.

Definition I_exists (A : Type) (P : A → IProp) : IProp :=
  mk_IProp (I_exists_func A P) (I_exists_func_monotone A P).

Notation "'∃ᵢ' x .. y , P" :=
  (I_exists _ (fun x => .. (I_exists _ (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity).

Lemma I_exists_intro {n : nat} {A : Type} {P : A → IProp} :
  ∀ x : A, (n ⊨ P x) → (n ⊨ ∃ᵢ x, P x).
Proof.
intros x H; apply I_valid_intro; simpl; eexists; eassumption.
Qed.

Lemma I_exists_elim {n : nat} {A : Type} {P : A → IProp} :
  (n ⊨ ∃ᵢ x, P x) → ∃ x, (n ⊨ P x).
Proof.
intro H; apply I_valid_elim in H; apply H.
Qed.

(* ========================================================================= *)
(* Tactics *)

Ltac idestruct_exists H x H' :=
  apply I_exists_elim in H;
  destruct H as [x H'].

Ltac iexists x :=
  apply (I_exists_intro x); isimplP.