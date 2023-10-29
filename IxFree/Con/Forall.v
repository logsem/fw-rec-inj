Require Import Utf8.
Require Import IxFree.Base.

Definition I_forall_func (A : Type) (P : A → IProp) : nat → Prop :=
  λ n, ∀ x : A, n ⊨ P x.
Lemma I_forall_func_monotone (A : Type) (P : A → IProp) :
  monotone (I_forall_func A P).
Proof.
unfold monotone; unfold I_forall_func; intros n H₁ x.
apply I_valid_monotone_S; auto.
Qed.

Definition I_forall (A : Type) (P : A → IProp) : IProp :=
  mk_IProp (I_forall_func A P) (I_forall_func_monotone A P).

Notation "'∀ᵢ' x .. y , P" :=
  (I_forall _ (fun x => .. (I_forall _ (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity).

Lemma I_forall_intro {n : nat} {A : Type} {P : A → IProp} :
  (∀ x : A, (n ⊨ P x)) → (n ⊨ ∀ᵢ x, P x).
Proof.
intro H; apply I_valid_intro; intro x; auto.
Qed.

Lemma I_forall_elim {n : nat} {A : Type} {P : A → IProp} :
  (n ⊨ ∀ᵢ x : A, P x) → ∀ x, n ⊨ P x.
Proof.
intros H x; apply I_valid_elim in H; apply H.
Qed.

(* ========================================================================= *)
(* Tactics *)

Ltac iintro_forall_named x :=
  apply I_forall_intro; intro x.

Ltac iintro_forall_anon :=
  apply I_forall_intro; intro.