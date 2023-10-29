Require Import Utf8.

Definition monotone (P : nat → Prop) := ∀ n, P (S n) → P n.

Module Type IProp_S.

Parameter IProp : Type.

Parameter mk_IProp : ∀ P : nat → Prop, monotone P → IProp.

Parameter I_valid_at : nat -> IProp -> Prop.

Section I_valid.
Variable P : nat → Prop.
Variable H : monotone P.
Variable n : nat.

Parameter I_valid_intro : P n → I_valid_at n (mk_IProp P H).
Parameter I_valid_elim  : I_valid_at n (mk_IProp P H) → P n.
End I_valid.

Parameter I_valid_monotone_S : ∀ (P : IProp) (n : nat),
  I_valid_at (S n) P → I_valid_at n P.

End IProp_S.

Module IProp : IProp_S.

Definition IProp := { P : nat → Prop | monotone P }.

Definition mk_IProp (P : nat → Prop) (H : monotone P) :=
  exist _ P H.

Definition I_valid_at (n : nat) (P : IProp) : Prop :=
  proj1_sig P n.

Section I_valid.
Variable P : nat → Prop.
Variable H : monotone P.
Variable n : nat.

Lemma I_valid_intro : P n → I_valid_at n (mk_IProp P H).
Proof. auto. Qed.
Lemma I_valid_elim  : I_valid_at n (mk_IProp P H) → P n.
Proof. auto. Qed.
End I_valid.

Lemma I_valid_monotone_S (P : IProp) (n : nat) :
  I_valid_at (S n) P → I_valid_at n P.
Proof.
destruct P as [ P H ]; apply H.
Qed.

End IProp.

Include IProp.

Inductive IRelSig : Type :=
| S_IProp  : IRelSig
| S_Forall : ∀ A : Type, (A → IRelSig) → IRelSig
.

Delimit Scope irel_sig_scope with irel_sig.

Notation "*ₛ" := S_IProp : irel_sig_scope.
Notation "A '→ₛ' B" := (S_Forall A (fun _ => B))
  (right associativity, at level 90) : irel_sig_scope.
Notation "∀ₛ x .. y , Σ" :=
  (S_Forall _ (fun x => .. (S_Forall _ (fun y => Σ)) .. ))
  (at level 200, x binder, y binder, right associativity) : irel_sig_scope.

Local Open Scope irel_sig_scope.

Fixpoint IRel (Σ : IRelSig) : Type :=
  match Σ with
  | *ₛ           => IProp
  | S_Forall A F => ∀ x : A, IRel (F x)
  end.

Definition I_valid (P : IProp) := ∀ n, I_valid_at n P.

Notation "n ⊨ P" := (I_valid_at n P) (at level 98, no associativity).
Notation "⊨ P" := (I_valid P) (at level 98, no associativity).

Lemma I_valid_monotone (P : IProp) (n m : nat) :
  n ≤ m → (m ⊨ P) → (n ⊨ P).
Proof.
induction 1; trivial.
intro; apply IHle; apply I_valid_monotone_S; assumption.
Qed.

(* ========================================================================= *)
(* Embedding Prop *)

Definition I_Prop (P : Prop) : IProp := mk_IProp (λ _, P) (λ _ H, H).

Notation "( P )ᵢ" := (I_Prop P).

Lemma I_Prop_intro (P : Prop) n : P → (n ⊨ (P)ᵢ).
Proof.
intro H; apply I_valid_intro; assumption.
Qed.

Lemma I_Prop_elim (P : Prop) n : (n ⊨ (P)ᵢ) → P.
Proof.
intro H; apply I_valid_elim in H; apply H.
Qed.

Ltac isimplP :=
  repeat match goal with
         | [H : ?n ⊨ (?P)ᵢ |- _] => apply I_Prop_elim in H
         | |- ?n ⊨ (?P)ᵢ => apply I_Prop_intro
         end.

(* ========================================================================= *)
(* Generalized relation tactics *)

Class RelationContext {A : Type} (f : A → Prop).

Class CReflexive {A B : Type} f {GR : RelationContext f} (R : A → A → B) :=
  creflexivity : ∀ x : A, f (R x x).

Class CSymmetric {A B : Type} f {GR : RelationContext f} (R : A → A → B) :=
  csymmetry (x y : A) (HR : f (R x y)) : f (R y x).

Class CTransitive  {A B : Type} f {GR : RelationContext f} (R : A → A → B) :=
  ctransitivity (x y z : A) (HR₁ : f (R x y)) (HR₂ : f (R y z)) : f (R x z).

Instance RC_Ivalat n : RelationContext (I_valid_at n).
Proof.
Qed.
Instance RC_Ival : RelationContext I_valid.
Proof.
Qed.

Instance CRefl_Ivalat_Ival {A} (r : A → A → IProp) (HR : forall n, CReflexive (I_valid_at n) r) :
  CReflexive I_valid r.
Proof.
  intros x n; now specialize (HR n x).
Qed.

Instance CSymm_Ivalat_Ival {A} (r : A → A → IProp) (HR : forall n, CSymmetric (I_valid_at n) r) :
  CSymmetric I_valid r.
Proof.
  intros x y Hxy n; apply HR, Hxy.
Qed.

Instance CTrans_Ivalat_Ival {A} (r : A → A → IProp) (HR : forall n, CTransitive (I_valid_at n) r) :
  CTransitive I_valid r.
Proof.
  intros x y z Hxy Hyz n; eapply HR; [apply Hxy | apply Hyz].
Qed.

Tactic Notation "creflexivity"   := apply creflexivity.
Tactic Notation "csymmetry"      := apply csymmetry.
Tactic Notation "ctransitivity" constr(t) := apply ctransitivity with (y := t).
Tactic Notation "cetransitivity" := eapply ctransitivity.
