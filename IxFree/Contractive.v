Require Import Utf8.
Require Import IxFree.Base IxFree.Connectives IxFree.Relations.

Definition contractive (Σ : IRelSig) (f : IRel Σ → IRel Σ) : Prop :=
  ∀ R₁ R₂, ⊨ ▷(R₁ ≈ᵢ R₂) ⇒ f R₁ ≈ᵢ f R₂.

Lemma auto_contr_id (n : nat) (P : IProp) :
  n ⊨ P ⇔ P.
Proof.
isplit; iintro; assumption.
Qed.

Lemma auto_contr_arrow (n : nat) (P₁ Q₁ P₂ Q₂ : IProp) :
 (n ⊨ P₁ ⇔ P₂) → (n ⊨ Q₁ ⇔ Q₂) → (n ⊨ (P₁ ⇒ Q₁) ⇔ (P₂ ⇒ Q₂)).
Proof.
intros HP HQ; isplit; iintro H1; iintro H2.
+ apply I_conj_elim1 in HQ; iapply HQ; iapply H1.
  apply I_conj_elim2 in HP; iapply HP; assumption.
+ apply I_conj_elim2 in HQ; iapply HQ; iapply H1.
  apply I_conj_elim1 in HP; iapply HP; assumption.
Qed.

Lemma auto_contr_conj (n : nat) (P₁ Q₁ P₂ Q₂ : IProp) :
  (n ⊨ P₁ ⇔ P₂) → (n ⊨ Q₁ ⇔ Q₂) → (n ⊨ P₁ ∧ᵢ Q₁ ⇔ P₂ ∧ᵢ Q₂).
Proof.
intros HP HQ; isplit; iintro H; isplit.
+ apply I_conj_elim1 in HP; iapply HP; eapply I_conj_elim1; eassumption.
+ apply I_conj_elim1 in HQ; iapply HQ; eapply I_conj_elim2; eassumption.
+ apply I_conj_elim2 in HP; iapply HP; eapply I_conj_elim1; eassumption.
+ apply I_conj_elim2 in HQ; iapply HQ; eapply I_conj_elim2; eassumption.
Qed.

Lemma auto_contr_disj (n : nat) (P₁ Q₁ P₂ Q₂ : IProp) :
  (n ⊨ P₁ ⇔ P₂) → (n ⊨ Q₁ ⇔ Q₂) → (n ⊨ P₁ ∨ᵢ Q₁ ⇔ P₂ ∨ᵢ Q₂).
Proof.
intros HP HQ; isplit; iintro H; idestruct H as H H.
+ ileft;  apply I_conj_elim1 in HP; iapply HP; assumption.
+ iright; apply I_conj_elim1 in HQ; iapply HQ; assumption.
+ ileft;  apply I_conj_elim2 in HP; iapply HP; assumption.
+ iright; apply I_conj_elim2 in HQ; iapply HQ; assumption.
Qed.

Lemma auto_contr_iff (n : nat) (P₁ Q₁ P₂ Q₂ : IProp) :
  (n ⊨ P₁ ⇔ P₂) → (n ⊨ Q₁ ⇔ Q₂) → (n ⊨ (P₁ ⇔ Q₁) ⇔ (P₂ ⇔ Q₂)).
Proof.
intros HP HQ; apply auto_contr_conj; apply auto_contr_arrow; assumption.
Qed.

Lemma auto_contr_forall (n : nat) (A : Type) (P₁ P₂ : A → IProp) :
  (∀ x : A, n ⊨ P₁ x ⇔ P₂ x) → (n ⊨ (∀ᵢ x : A, P₁ x) ⇔ (∀ᵢ x : A, P₂ x)).
Proof.
intro HP; apply I_forall_intro in HP; isplit; iintro H.
+ iintro x; ispecialize HP x.
  apply I_conj_elim1 in HP; iapply HP; iapply H.
+ iintro x; ispecialize HP x.
  apply I_conj_elim2 in HP; iapply HP; iapply H.
Qed.

Lemma auto_contr_exists (n : nat) (A : Type) (P₁ P₂ : A → IProp) :
  (∀ x : A, n ⊨ P₁ x ⇔ P₂ x) → (n ⊨ (∃ᵢ x : A, P₁ x) ⇔ (∃ᵢ x : A, P₂ x)).
Proof.
intro HP; apply I_forall_intro in HP; isplit; iintro H.
+ idestruct H as x H; iexists x.
  iespecialize HP; apply I_conj_elim1 in HP; iapply HP; assumption.
+ idestruct H as x H; iexists x.
  iespecialize HP; apply I_conj_elim2 in HP; iapply HP; assumption.
Qed.

Ltac auto_contr :=
  match goal with
  | [ |- ?N ⊨ ?P ⇔ ?P ] =>
    apply (auto_contr_id N P)
  | [ |- ?N ⊨ (?P1 ⇒ ?Q1) ⇔ (?P2 ⇒ ?Q2) ] =>
    apply (auto_contr_arrow N P1 Q1 P2 Q2); auto_contr
  | [ |- ?N ⊨ ?P1 ∧ᵢ ?Q1 ⇔ ?P2 ∧ᵢ ?Q2 ] =>
    apply (auto_contr_conj N P1 Q1 P2 Q2); auto_contr
  | [ |- ?N ⊨ ?P1 ∨ᵢ ?Q1 ⇔ ?P2 ∨ᵢ ?Q2 ] =>
    apply (auto_contr_disj N P1 Q1 P2 Q2); auto_contr
  | [ |- ?N ⊨ (?P1 ⇔ ?Q1) ⇔ (?P2 ⇔ ?Q2) ] =>
    apply (auto_contr_iff N P1 Q1 P2 Q2); auto_contr
  | [ |- ?N ⊨ (∀ᵢ _, _) ⇔ (∀ᵢ _, _) ] =>
    apply auto_contr_forall; intro; auto_contr
  | [ |- ?N ⊨ (∃ᵢ _, _) ⇔ (∃ᵢ _, _) ] =>
    apply auto_contr_exists; intro; auto_contr
  | [ |- ?N ⊨ (▷ _) ⇔ (▷ _) ] =>
    later_up; later_shift; auto_contr
  | _ => idtac
  end.