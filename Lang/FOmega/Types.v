Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic Binding.Auto.
Require Import Eqdep Eqdep_dec.
Require Import Basics RelationClasses.

(** Syntax of kinds and types of System Fω, and the type equivalence judgment *)

Inductive kind :=
| KTyp
| KArr (κ₁ κ₂ : kind) : kind.

Module kindEqDec <: DecidableType.
  Definition U := kind.

  Lemma eq_dec : ∀ x y:U, {x = y} + {x <> y}.
  Proof.
    decide equality.
  Qed.
End kindEqDec.

Notation "⋆" := KTyp.
Notation "κ₁ ⇒ κ₂" := (KArr κ₁ κ₂) (at level 45, right associativity).

Module Export DED_typ := DecidableEqDep (kindEqDec).

Inductive tconst : kind → Type :=
| tc_unit : tconst ⋆
| tc_void : tconst ⋆
| tc_prod : tconst (⋆ ⇒ ⋆ ⇒ ⋆)
| tc_sum  : tconst (⋆ ⇒ ⋆ ⇒ ⋆)
| tc_arr  : tconst (⋆ ⇒ ⋆ ⇒ ⋆)
| tc_all  κ : tconst ((κ ⇒ ⋆) ⇒ ⋆)
| tc_xist κ : tconst ((κ ⇒ ⋆) ⇒ ⋆).

Inductive type {Δ : Ctx kind} : kind → Type :=
| t_var {κ} (x : dom Δ) (EQ : Δ x = κ) : type κ
| t_lam {κₐ κᵣ} (τ : @type (Δ ▹ κₐ) κᵣ) : type (κₐ ⇒ κᵣ)
| t_app {κₐ κᵣ} (σ : type (κₐ ⇒ κᵣ)) (τ : type κₐ) : type κᵣ
| t_const {κ} (c : tconst κ) : type κ.
Arguments type Δ : clear implicits.
(* this gets the arguments in the right order for our typeclass magic *)
Definition typ := flip type.

Local Open Scope bind_scope.

#[export] Instance IPC_typ : IntPureCore typ := @t_var.

Fixpoint tmap {κ} {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (τ : typ κ Δ₁) : typ κ Δ₂ :=
  match τ with
  | t_var x EQ => t_var (δ x) (eq_trans (arr_hom δ x) EQ)
  | t_lam τ => t_lam (tmap (δ ↑) τ)
  | t_app σ τ => t_app (tmap δ σ) (tmap δ τ)
  | t_const c => t_const c
  end.
#[export] Instance FMap_typ {κ : kind} : FunctorCore (typ κ) := @tmap κ.

Fixpoint tbind {κ} {Δ₁ Δ₂ : Ctx kind} (ρ : Δ₁ [⇒] Δ₂) (τ : typ κ Δ₁) : typ κ Δ₂ :=
  match τ with
  | t_var x EQ => ρ _ x EQ
  | t_lam τ => t_lam (tbind (ρ ↑) τ)
  | t_app σ τ => t_app (tbind ρ σ) (tbind ρ τ)
  | t_const c => t_const c
  end.
#[export] Instance BindCore_typ {κ} : BindCore (typ κ) := @tbind κ.

#[export] Instance IP_typ : IntPure typ.
Proof.
  split; intros; term_simpl; reflexivity.
Qed.

Lemma tvar_ext {κ Δ} {x y : dom Δ} (EQx : Δ x = κ) (EQy : Δ y = κ) (EQ : x = y) :
  t_var x EQx = t_var y EQy.
Proof.
  subst y; destruct EQy; now rewrite UIP_refl with (p := EQx).
Qed.

Fixpoint tmap_id {κ} Δ (δ : Δ [→] Δ) (τ : typ κ Δ) : δ ≡ ı → fmap δ τ = τ.
Proof.
  auto_map_id; [].
  apply tvar_ext, EQ.
Qed.

Fixpoint tmap_comp {κ} (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (τ : typ κ A) :
  f ∘ g ≡ h → fmap f (fmap g τ) = fmap h τ.
Proof.
  auto_map_comp; [].
  apply tvar_ext, EQ.
Qed.

#[export] Instance Functor_typ {κ} : Functor (typ κ).
Proof.
  split; [exact tmap_id | exact tmap_comp].
Qed.

Fixpoint tmap_tbind_pure {κ} (A B : Ctx kind) (f : A [→] B) (g : A [⇒] B) (τ : typ κ A) :
  f ̂ ≡ g → fmap f τ = bind g τ.
Proof.
  auto_map_bind_pure.
Qed.

#[export] Instance BindMapPure_typ {κ} : BindMapPure (typ κ).
Proof.
  split; exact tmap_tbind_pure.
Qed.

Fixpoint tmap_tbind_comm {κ} (A B₁ B₂ C : Ctx kind) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
         (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (τ : typ κ A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ τ) = fmap f₁ (bind g₁ τ).
Proof.
  auto_map_bind_comm.
Qed.

#[export] Instance BindMapComm_typ {κ} : BindMapComm (typ κ).
Proof.
  split; exact tmap_tbind_comm.
Qed.

Fixpoint tbind_id {κ} (A : Ctx kind) (f : A [⇒] A) (τ : typ κ A) :
  f ≡ ı → bind f τ = τ.
Proof.
  auto_bind_id.
Qed.

Fixpoint tbind_comp {κ} (A B C : Ctx kind) (f : B [⇒] C) (g : A [⇒] B) h (τ : typ κ A) :
  f ∘ g ≡ h → bind f (bind g τ) = bind h τ.
Proof.
  auto_bind_comp.
Qed.

Instance Bind_expr {κ} : Bind (typ κ).
Proof.
  split; [exact tbind_id | exact tbind_comp].
Qed.

Inductive tequiv (Δ : Ctx kind) : ∀ κ : kind, typ κ Δ → typ κ Δ → Prop :=
| te_var κ (x : dom Δ) (EQ₁ EQ₂ : Δ x = κ) : tequiv Δ κ (t_var x EQ₁) (t_var x EQ₂)
| te_lam {κₐ κᵣ τ₁ τ₂} (HE : tequiv (Δ ▹ κₐ) κᵣ τ₁ τ₂) :
    tequiv Δ (κₐ ⇒ κᵣ) (t_lam τ₁) (t_lam τ₂)
| te_app {κₐ κᵣ σ₁ σ₂ τ₁ τ₂}
         (HEσ : tequiv Δ (κₐ ⇒ κᵣ) σ₁ σ₂)
         (HEτ : tequiv Δ κₐ τ₁ τ₂) :
    tequiv Δ κᵣ (t_app σ₁ τ₁) (t_app σ₂ τ₂)
| te_const {κ} (c : tconst κ) : tequiv Δ κ (t_const c) (t_const c)
| te_symm {κ τ₁ τ₂} (HE : tequiv Δ κ τ₁ τ₂) : tequiv Δ κ τ₂ τ₁
| te_trans {κ τ₁ τ₂ τ₃} (HE₁ : tequiv Δ κ τ₁ τ₂) (HE₂ : tequiv Δ κ τ₂ τ₃) : tequiv Δ κ τ₁ τ₃
| te_eta {κₐ κᵣ} (τ : typ (κₐ ⇒ κᵣ) Δ) :
    tequiv Δ (κₐ ⇒ κᵣ) τ (t_lam (t_app (shift τ) (t_var (VZ : dom (_ ▹ _)) eq_refl)))
| te_beta {κₐ κᵣ} (σ : typ κᵣ (Δ ▹ κₐ)) (τ : typ κₐ Δ) :
    tequiv Δ κᵣ (t_app (t_lam σ) τ) (subst σ τ).

#[export] Instance Equiv_teq {Δ : Ctx kind} {κ} : Equivalence (tequiv Δ κ).
Proof.
  split; [| intros τ₁ τ₂; now apply te_symm | intros τ₁ τ₂ τ₃; now apply te_trans].
  intros τ; induction τ; eauto using tequiv.
Qed.
