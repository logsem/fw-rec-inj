Require Export IxFree.Con.Arrow.
Require Export IxFree.Con.Conj.
Require Export IxFree.Con.Disj.
Require Export IxFree.Con.Iff.
Require Export IxFree.Con.Forall.
Require Export IxFree.Con.Exists.
Require Export IxFree.Con.Later.
Require Export IxFree.Con.Tactics.


(* =============================== *)
(* Additional derivable properties *)
Require Import Utf8.
Require Import IxFree.Base.

Lemma I_iff_conj_distr (P Q R S : IProp) n
      (HH : n ⊨ (P ⇔ R) ∧ᵢ (Q ⇔ S)) :
  n ⊨ P ∧ᵢ Q ⇔ R ∧ᵢ S.
Proof.
  idestruct HH as HPR HQS; isplit; iintro H; isplit.
  - idestruct HPR as H₁ H₂; iapply H₁; idestruct H as HP HQ; assumption.
  - idestruct HQS as H₁ H₂; iapply H₁; idestruct H as HP HQ; assumption.
  - idestruct HPR as H₁ H₂; iapply H₂; idestruct H as HR HS; assumption.
  - idestruct HQS as H₁ H₂; iapply H₂; idestruct H as HR HS; assumption.
Qed.

Lemma I_iff_all_distr {A : Type} (P Q : A → IProp) n
      (HH : n ⊨ ∀ᵢ x : A, P x ⇔ Q x) :
  n ⊨ (∀ᵢ x, P x) ⇔ (∀ᵢ x, Q x).
Proof.
  isplit; iintro H; iintro x; ispecialize HH x; ispecialize H x;
    idestruct HH as H₁ H₂; [iapply H₁ | iapply H₂]; assumption.
Qed.

Lemma I_iff_impl_distr (P Q R S : IProp) n
      (HH : n ⊨ P ⇔ Q)
      (HT : n ⊨ (R ⇔ S)) :
  n ⊨ (P ⇒ R) ⇔ (Q ⇒ S).
Proof.
  isplit; iintro HJ; iintro HA; idestruct HH as HH₁ HH₂.
  - idestruct HT as HT₁ HT₂; iapply HT₁; iapply HJ; iapply HH₂; assumption.
  - idestruct HT as HT₁ HT₂; iapply HT₂; iapply HJ; iapply HH₁; assumption.
Qed.

Lemma I_iff_disj_distr (P Q R S : IProp) n
      (HPQ : n ⊨ P ⇔ Q)
      (HRS : n ⊨ R ⇔ S) :
  n ⊨ (P ∨ᵢ R) ⇔ (Q ∨ᵢ S).
Proof.
  isplit; iintro HJ; idestruct HPQ as HPQ₁ HPQ₂; idestruct HRS as HRS₁ HRS₂; idestruct HJ as HJ₁ HJ₂.
  - ileft; now iapply HPQ₁.
  - iright; now iapply HRS₁.
  - ileft; now iapply HPQ₂.
  - iright; now iapply HRS₂.
Qed.
