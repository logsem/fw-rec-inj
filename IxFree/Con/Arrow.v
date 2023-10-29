Require Import Utf8.
Require Import IxFree.Base.

Definition I_arrow_func (P Q : IProp) : nat → Prop :=
  λ n, ∀ k, k ≤ n → (k ⊨ P) → (k ⊨ Q).
Lemma I_arrow_func_monotone (P Q : IProp) :
  monotone (I_arrow_func P Q).
Proof.
unfold monotone; intros n H₁ k k_le_n.
apply H₁; constructor; assumption.
Qed.

Definition I_arrow (P Q : IProp) : IProp :=
  mk_IProp (I_arrow_func P Q) (I_arrow_func_monotone P Q).

Notation "A ⇒ B" := (I_arrow A B) (at level 90, right associativity).

Lemma I_arrow_intro {n : nat} {P Q : IProp} :
  (∀ k, k ≤ n → (k ⊨ P) → (k ⊨ Q)) → (n ⊨ (P ⇒ Q)).
Proof.
intro H; apply I_valid_intro; simpl; unfold I_arrow_func; apply H.
Qed.

Lemma I_arrow_elim {n : nat} {P Q : IProp} :
  (n ⊨ P ⇒ Q) → (n ⊨ P) → (n ⊨ Q).
Proof.
intro Hf; apply I_valid_elim in Hf; simpl in Hf; unfold I_arrow_func in Hf.
apply Hf; trivial.
Qed.

(* ========================================================================= *)
(* Tactics *)

Ltac iintro_arrow_named H :=
  apply I_arrow_intro;
  let K := fresh "K" in
  let L := fresh "L" in
  intros K L H;
  let TL := type of L in
  let N := match TL with _ ≤ ?N => N end in
  repeat 
    match goal with
    | [ A : N ⊨ ?R |- _ ] => 
      apply (I_valid_monotone R K N L) in A
      end;
  clear L;
  clear N;
  rename K into N.

Ltac iintro_arrow_anon :=
  let H := fresh "H" in
  iintro_arrow_named H.

Instance CRefl_Iarr n : CReflexive (I_valid_at n) I_arrow.
Proof.
  intros x; apply I_arrow_intro; now auto.
Qed.

Instance CTrans_IArr n : CTransitive (I_valid_at n) I_arrow.
Proof.
  intros x y z HR₁ HR₂; apply I_arrow_intro; intros.
  eapply I_arrow_elim; [eapply I_valid_monotone; eassumption |].
  eapply I_arrow_elim; [eapply I_valid_monotone |]; eassumption.
Qed.
