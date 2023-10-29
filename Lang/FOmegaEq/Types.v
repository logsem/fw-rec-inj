Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic Binding.Auto.
Require Import FOmegaEq.Kinds.

(* Well-kinded types and constraints (Fig. 2) *)
Inductive type {Δ : Ctx kind} : kind → Type :=
| t_var κ (x : dom Δ) (EQ : Δ x = κ) : type κ
| t_lam {κₐ κᵣ} (τ : @type (Δ ▹ κₐ) κᵣ) : type (κₐ ⇒ κᵣ)
| t_app {κₐ κᵣ} (σ : type (κₐ ⇒ κᵣ)) (τ : type κₐ) : type κᵣ
| t_ctor {κ} (c : tctor κ) : type κ
| t_carr  (ψ : constr) (τ : type ⋆) : type ⋆
| t_cprod (ψ : constr) (τ : type ⋆) : type ⋆
with constr {Δ : Ctx kind} : Type :=
| c_eq (κ : kind) (τ₁ τ₂ : type κ) : constr.
Arguments type Δ : clear implicits.
Arguments constr Δ : clear implicits.

Require Import Basics.

Definition typ := flip type.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Coercion t_ctor : tctor >-> type.
Coercion t_app : type >-> Funclass.

Definition rec_type (Δ : Ctx kind) (κ : kind) (τ : typ κ (extC κ Δ)) : typ κ Δ
  := (tc_rec κ) (t_lam τ).

Definition t_arr {Δ} (τ₁ τ₂ : typ ⋆ Δ) : typ ⋆ Δ :=
  tc_arr τ₁ τ₂.

Definition t_prod {Δ} (τ₁ τ₂ : typ ⋆ Δ) : typ ⋆ Δ :=
  tc_prod τ₁ τ₂.

Definition t_sum {Δ} (τ₁ τ₂ : typ ⋆ Δ) : typ ⋆ Δ :=
  tc_sum τ₁ τ₂.

Definition t_all {Δ} κ (τ : typ ⋆ (extC κ Δ)) :=
  (tc_all κ) (t_lam τ).

Definition t_xist {Δ} κ (τ : typ ⋆ (extC κ Δ)) :=
  (tc_xist κ) (t_lam τ).

Notation "'ƛ' τ" := (t_lam τ : typ _ _) (at level 60) : typ_scope.
Notation "σ →ᵗ τ" := (t_arr σ τ) (at level 55, right associativity) : typ_scope.
Notation "τ₁ + τ₂" := (t_sum τ₁ τ₂) (at level 50, left associativity) : typ_scope.
Notation "τ₁ × τ₂" := (t_prod τ₁ τ₂) (at level 40, left associativity) : typ_scope.
Notation "χ →ᶜ τ" := (t_carr χ τ) (at level 55, right associativity) : typ_scope.
Notation "χ ×ᶜ τ" := (t_cprod χ τ) (at level 40, left associativity) : typ_scope.
Notation "τ₁ ≃ τ₂" := (c_eq _ τ₁ τ₂) (at level 65, no associativity) : typ_scope.
Notation "∀ᵗ κ , τ" := (t_all κ τ) (at level 60) : typ_scope.
Notation "∃ᵗ κ , τ" := (t_xist κ τ) (at level 60) : typ_scope.
Notation "⊥" := tc_void : typ_scope.
Notation "'⊤'" := tc_unit : typ_scope.
Notation "'0ᵛ'" := (t_var _ (VZ : dom (_ ▹ _)) eq_refl).

Local Open Scope bind_scope.
Local Open Scope typ_scope.

Fixpoint tmap {κ} {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (τ : typ κ Δ₁) : typ κ Δ₂ :=
  match τ with
  | t_var κ x EQ => t_var κ (δ x) (eq_trans (arr_hom δ x) EQ)
  | t_lam τ => ƛ tmap (δ ↑) τ
  | t_app σ τ => (tmap δ σ) (tmap δ τ)
  | t_ctor c  => c
  | φ →ᶜ τ => cmap δ φ →ᶜ tmap δ τ
  | φ ×ᶜ τ => cmap δ φ ×ᶜ tmap δ τ
  end
with cmap {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (φ : constr Δ₁) : constr Δ₂ :=
  match φ with
  | c_eq κ τ₁ τ₂ => c_eq κ (tmap δ τ₁) (tmap δ τ₂)
  end.

#[export] Instance IPC_typ : IntPureCore (λ κ, typ κ) := @t_var.
#[export] Instance FMap_typ {κ} : FunctorCore (typ κ) := @tmap κ.
#[export] Instance FMap_constr : FunctorCore constr := @cmap.

Fixpoint tbind {κ} {Δ₁ Δ₂ : Ctx kind} (ρ : Δ₁ [⇒] Δ₂) (τ : typ κ Δ₁) : typ κ Δ₂ :=
  match τ with
  | t_var κ x EQ  => ρ κ x EQ
  | t_lam τ     => ƛ (tbind (ρ ↑) τ)
  | t_app σ τ   => (tbind ρ σ) (tbind ρ τ)
  | t_ctor c    => c
  | t_carr  φ τ => cbind ρ φ →ᶜ tbind ρ τ
  | t_cprod φ τ => cbind ρ φ ×ᶜ tbind ρ τ
  end
with cbind {Δ₁ Δ₂ : Ctx kind} (ρ : Δ₁ [⇒] Δ₂) (φ : constr Δ₁) : constr Δ₂ :=
  match φ with
  | c_eq κ τ₁ τ₂ => c_eq κ (tbind ρ τ₁) (tbind ρ τ₂)
  end.
#[export] Instance BindT {κ} : BindCore (typ κ) := @tbind κ.
#[export] Instance BindC : BindCore constr := @cbind.

Lemma tvar_ext {κ Δ} {x y : dom Δ} (EQx : Δ x = κ) (EQy : Δ y = κ) (EQ : x = y) :
  t_var κ x EQx = t_var κ y EQy.
Proof.
  subst y; destruct EQy; now rewrite UIP_refl with (p := EQx).
Qed.

#[export] Instance IP_typ : IntPure typ.
Proof.
  split; intros; term_simpl; reflexivity.
Qed.

Fixpoint tmap_id {κ} Δ (δ : Δ [→] Δ) (τ : typ κ Δ) : δ ≡ ı → fmap δ τ = τ
with cmap_id Δ (δ : Δ [→] Δ) (φ : constr Δ) : δ ≡ ı → fmap δ φ = φ.
Proof.
  - auto_map_id; [].
    apply tvar_ext, EQ.
  - auto_map_id.
Qed.

Fixpoint tmap_comp {κ} (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (τ : typ κ A) :
  f ∘ g ≡ h → fmap f (fmap g τ) = fmap h τ
with cmap_comp (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (φ : constr A) :
  f ∘ g ≡ h → fmap f (fmap g φ) = fmap h φ.
Proof.
  - auto_map_comp; [].
    apply tvar_ext, EQ.
  - auto_map_comp.
Qed.

#[export] Instance Functor_typ {κ} : Functor (typ κ).
Proof.
  split; [exact tmap_id | exact tmap_comp].
Qed.
#[export] Instance Functor_constr : Functor constr.
Proof.
  split; [exact cmap_id | exact cmap_comp].
Qed.

Fixpoint tmap_tbind_pure {κ} (A B : Ctx kind) (f : A [→] B) (g : A [⇒] B) (τ : typ κ A) :
  f ̂ ≡ g → fmap f τ = bind g τ
with cmap_cbind_pure (A B : Ctx kind) (f : A [→] B) (g : A [⇒] B) (φ : constr A) :
  f ̂ ≡ g → fmap f φ = bind g φ.
Proof.
  - auto_map_bind_pure.
  - auto_map_bind_pure.
Qed.

#[export] Instance BindMapPure_typ {κ} : BindMapPure (typ κ).
Proof.
  split; intros; now apply tmap_tbind_pure.
Qed.
#[export] Instance BindMapPure_constr : BindMapPure constr.
Proof.
  split; intros; now apply cmap_cbind_pure.
Qed.

Fixpoint tmap_tbind_comm {κ} (A B₁ B₂ C : Ctx kind) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
         (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (τ : typ κ A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ τ) = fmap f₁ (bind g₁ τ)
with cmap_cbind_comm (A B₁ B₂ C : Ctx kind) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
                     (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (φ : constr A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ φ) = fmap f₁ (bind g₁ φ).
Proof.
  - auto_map_bind_comm.
  - auto_map_bind_comm.
Qed.

#[export] Instance BindMapComm_typ {κ} : BindMapComm (typ κ).
Proof.
  split; intros; now apply tmap_tbind_comm.
Qed.
#[export] Instance BindMapComm_constr : BindMapComm constr.
Proof.
  split; intros; now apply cmap_cbind_comm.
Qed.

Fixpoint tbind_id {κ} (A : Ctx kind) (f : A [⇒] A) (τ : typ κ A) :
  f ≡ ı → bind f τ = τ
with cbind_id  (A : Ctx kind) (f : A [⇒] A) (φ : constr A) :
  f ≡ ı → bind f φ = φ.
Proof.
  - auto_bind_id.
  - auto_bind_id.
Qed.

Fixpoint tbind_comp {κ} (A B C : Ctx kind) (f : B [⇒] C) (g : A [⇒] B) h (τ : typ κ A) :
  f ∘ g ≡ h → bind f (bind g τ) = bind h τ
with cbind_comp (A B C : Ctx kind) (f : B [⇒] C) (g : A [⇒] B) h (φ : constr A) :
 f ∘ g ≡ h → bind f (bind g φ) = bind h φ.
Proof.
  - auto_bind_comp.
  - auto_bind_comp.
Qed.

#[export] Instance Bind_typ {κ} : Bind (typ κ).
Proof.
  split; intros; [now apply tbind_id | now apply tbind_comp].
Qed.
#[export] Instance Bind_constr : Bind constr.
Proof.
  split; intros; [now apply cbind_id | now apply cbind_comp].
Qed.

Inductive rel_app {Δ : Ctx kind} (κ₁ : kind) (σ₁ σ₂ : typ κ₁ Δ) : ∀ κ₂, typ κ₂ Δ → typ κ₂ Δ → Prop :=
| rel_app_refl : rel_app κ₁ σ₁ σ₂ κ₁ σ₁ σ₂
| rel_app_app {κₐ κᵣ} (τ₁ τ₂ : typ (κₐ ⇒ κᵣ) Δ) (τ : typ κₐ Δ)
    (HF : rel_app κ₁ σ₁ σ₂ (κₐ ⇒ κᵣ) τ₁ τ₂) :
  rel_app κ₁ σ₁ σ₂ κᵣ (τ₁ τ) (τ₂ τ).

Require Import List.

Inductive tctd {Δ : Ctx kind} {κ} : typ κ Δ → ∀ {κ'}, tctor κ' → Prop :=
| inj_ctor c : tctd (t_ctor c) c
| inj_app {κₐ κ'} (σ : typ (κₐ ⇒ κ) Δ) τ (c : tctor κ') (HI : tctd σ c) : tctd (σ τ) c.

Inductive cdiscr : ∀ {κ}, tctor κ → tctor κ → Prop :=
| cd_unit_void : cdiscr tc_unit tc_void
| cd_void_unit : cdiscr tc_void tc_unit
| cd_all_xist κ : cdiscr (tc_all κ)  (tc_xist κ)
| cd_xist_all κ : cdiscr (tc_xist κ) (tc_all κ)
| cd_all_rec    : cdiscr (tc_all ⋆)  (tc_rec ⋆)
| cd_rec_all    : cdiscr (tc_rec ⋆)  (tc_all ⋆)
| cd_xist_rec   : cdiscr (tc_xist ⋆) (tc_rec ⋆)
| cd_rec_xist   : cdiscr (tc_rec ⋆)  (tc_xist ⋆)
| cd_arr_sum  : cdiscr tc_arr  tc_sum
| cd_sum_arr  : cdiscr tc_sum  tc_arr
| cd_arr_prod : cdiscr tc_arr  tc_prod
| cd_prod_arr : cdiscr tc_prod tc_arr
| cd_prod_sum : cdiscr tc_prod tc_sum
| cd_sum_prod : cdiscr tc_sum  tc_prod.

Definition cdiscrK {κ₁ κ₂} : tctor κ₁ → tctor κ₂ → Prop :=
  match kindEqDec.eq_dec κ₁ κ₂ with
  | left EQ =>
      eq_rect κ₁ (λ κ : kindEqDec.U, tctor κ₁ → tctor κ → Prop) cdiscr κ₂ EQ
  | right NEQ => λ _ _, True
  end.

(** Discriminability (Fig. 3, blue) *)
Inductive tdiscr {Δ : Ctx kind} : constr Δ → Prop :=
| td_ctd {κ κ₁ κ₂ τ₁ τ₂} {c₁ : tctor κ₁} {c₂ : tctor κ₂}
         (HI₁ : tctd τ₁ c₁)
         (HI₂ : tctd τ₂ c₂)
         (HD : cdiscrK c₁ c₂) :
  tdiscr (c_eq κ τ₁ τ₂)
| td_carr_ctd {ψ τ σ κ} {c : tctor κ}
              (HI : tctd σ c) :
  tdiscr (c_eq ⋆ (t_carr ψ τ) σ)
| td_ctd_carr {ψ τ σ κ} {c : tctor κ}
              (HI : tctd σ c) :
  tdiscr (c_eq ⋆ σ (t_carr ψ τ))
| td_cprod_ctd {ψ τ σ κ} {c : tctor κ}
               (HI : tctd σ c) :
  tdiscr (c_eq ⋆ (t_cprod ψ τ) σ)
| td_ctd_cprod {ψ τ σ κ} {c : tctor κ}
               (HI : tctd σ c) :
  tdiscr (c_eq ⋆ σ (t_cprod ψ τ))
| td_carr_cprod {ψ₁ ψ₂ τ₁ τ₂} :
    tdiscr (c_eq ⋆ (t_carr ψ₁ τ₁) (t_cprod ψ₂ τ₂))
| td_cprod_carr {ψ₁ ψ₂ τ₁ τ₂} :
    tdiscr (c_eq ⋆ (t_cprod ψ₂ τ₂) (t_carr ψ₁ τ₁)).
Notation "⊮ ψ" := (tdiscr ψ%typ) (at level 70).
Arguments tdiscr {Δ} ψ%typ.

Reserved Notation "Ψ ⊩ ψ" (at level 70, no associativity).

(* Provability (Fig. 3) *)
Inductive tproves_i {Δ : Ctx kind} {Ψ : list (constr Δ)} : constr Δ → Prop :=
| tpi_ax ψ (HIn : In ψ Ψ) : Ψ ⊩ ψ
| tpi_var {κ x EQ₁ EQ₂} : Ψ ⊩ t_var κ x EQ₁ ≃ t_var κ x EQ₂
| tpi_lam {κₐ κᵣ} {τ₁ τ₂ : typ κᵣ (Δ ▹ κₐ)} (HP : map shift Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ ƛ τ₁ ≃ ƛ τ₂
| tpi_app {κₐ κᵣ} {σ₁ σ₂ : typ (κₐ ⇒ κᵣ) Δ} {τ₁ τ₂}
          (HP₁ : Ψ ⊩ σ₁ ≃ σ₂)
          (HP₂ : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ σ₁ τ₁ ≃ σ₂ τ₂
| tpi_ctor {κ} (c : tctor κ) : Ψ ⊩ c ≃ c
| tpi_carr {ψ τ₁ τ₂} (HP : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ ψ →ᶜ τ₁ ≃ ψ →ᶜ τ₂
| tpi_cprod {ψ τ₁ τ₂} (HP : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ ψ ×ᶜ τ₁ ≃ ψ ×ᶜ τ₂
| tpi_symm {κ} {τ₁ τ₂ : typ κ Δ} (HP : Ψ ⊩ τ₁ ≃ τ₂) :
    Ψ ⊩ τ₂ ≃ τ₁
| tpi_trans {κ} {τ₁ τ₂ τ₃ : typ κ Δ}
            (HP₁ : Ψ ⊩ τ₁ ≃ τ₂)
            (HP₂ : Ψ ⊩ τ₂ ≃ τ₃) :
    Ψ ⊩ τ₁ ≃ τ₃
| tpi_eta {κₐ κᵣ} (τ : typ (κₐ ⇒ κᵣ) Δ) :
    Ψ ⊩ τ ≃ ƛ shift τ 0ᵛ
| tpi_beta {κₐ κᵣ} (σ : typ κₐ Δ) (τ : typ κᵣ (Δ ▹ κₐ)) :
    Ψ ⊩ (ƛ τ) σ ≃ subst τ σ
| tpi_appInjR {κₐ κᵣ κ} {σ₁ σ₂ : typ (κₐ ⇒ κᵣ) Δ} {c : tctor κ} {τ₁ τ₂ : typ κₐ Δ}
              (HI₁ : tctd σ₁ c)
              (HI₂ : tctd σ₂ c)
              (HP : Ψ ⊩ σ₁ τ₁ ≃ σ₂ τ₂) :
    Ψ ⊩ τ₁ ≃ τ₂
| tpi_appInjL {κₐ κᵣ κ} {σ₁ σ₂ : typ (κₐ ⇒ κᵣ) Δ} {c : tctor κ} {τ₁ τ₂ : typ κₐ Δ}
              (HI₁ : tctd σ₁ c)
              (HI₂ : tctd σ₂ c)
              (HP : Ψ ⊩ σ₁ τ₁ ≃ σ₂ τ₂) :
    Ψ ⊩ σ₁ ≃ σ₂
| tpi_carrInjR {ψ₁ ψ₂ τ₁ τ₂}                
                (HP : Ψ ⊩ ψ₁ →ᶜ τ₁ ≃ ψ₂ →ᶜ τ₂) :
    Ψ ⊩ (c_eq ⋆ τ₁ τ₂)
| tpi_cprodInjR {ψ₁ ψ₂ τ₁ τ₂}               
                (HP : Ψ ⊩ ψ₁ ×ᶜ τ₁ ≃ ψ₂ ×ᶜ τ₂) :
    Ψ ⊩ τ₁ ≃ τ₂
| tpi_cprodInjL {ψ₁ ψ₂ τ₁ τ₂}
    (HP : Ψ ⊩ ψ₁ ×ᶜ τ₁ ≃ ψ₂ ×ᶜ τ₂) :
    Ψ ⊩ ψ₁ -> Ψ ⊩ ψ₂
| tpi_carrInjL {ψ₁ ψ₂ τ₁ τ₂}
    (HP : Ψ ⊩ ψ₁ →ᶜ τ₁ ≃ ψ₂ →ᶜ τ₂) :
  Ψ ⊩ ψ₁ -> Ψ ⊩ ψ₂
where "Ψ ⊩ ψ" := (@tproves_i _ Ψ%typ ψ%typ).

Arguments tproves_i {Δ} Ψ%typ φ%typ.

Require Import RelationClasses.

#[export] Instance Irrefl_cdiscr {κ} : Irreflexive (@cdiscr κ).
Proof.
  intros c HD; inversion HD.
Qed.

#[export] Instance Symm_cdiscr {κ} : Symmetric (@cdiscr κ).
Proof.
  intros c₁ c₂ HD; destruct HD; now auto using @cdiscr.
Qed.

Class Separable {A : Type} (R : A → A → Prop) :=
  sep : ∀ {x y} z, R x y → R x z ∨ R z y.

#[export] Instance Sep_cdiscr {κ} : Separable (@cdiscr κ).
Proof.
  intros c₁ c₃ c₂ HD.
  assert (HT : ∀ κ' (EQ : κ' = κ) (c₂ : tctor κ'), cdiscr c₁ (eq_rect κ' tctor c₂ κ EQ) ∨ cdiscr (eq_rect κ' tctor c₂ κ EQ) c₃); [clear c₂; intros | exact (HT _ eq_refl c₂)].
  destruct HD; destruct c₂; inversion EQ; subst;
    rewrite !UIP_refl with (p := EQ); simpl; now auto using @cdiscr.
Qed.

Lemma tctd_det {Δ κ κ₁ κ₂ c₁ c₂} {τ : typ κ Δ} (HC₁ : tctd τ c₁) (HC₂ : tctd τ c₂) :
  existT tctor κ₁ c₁ = existT tctor κ₂ c₂.
Proof.
  induction HC₁.
  - remember (t_ctor c) as τ eqn: EQτ; destruct HC₂; [| discriminate].
    inversion EQτ; now symmetry.
  - remember (t_app σ τ) as τ' eqn: EQτ'; destruct HC₂; [discriminate |].
    inversion EQτ'; subst; apply inj_pairT2 in H1, H1, H2; subst σ0 τ0.
    now apply IHHC₁.
Qed.

#[export] Instance Irrefl_tdiscr {Δ κ} : Irreflexive (λ τ₁ τ₂, @tdiscr Δ (c_eq κ τ₁ τ₂)).
Proof.
  intros τ HD; inversion HD; subst;
  repeat match goal with
         | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pairT2 in H
         end; subst; try discriminate.
  - unfold cdiscrK in HD0; destruct (kindEqDec.eq_dec κ₁ κ₂) as [EQ | NEQ].
    + subst κ₂; simpl in HD0.
      assert (HT := tctd_det HI₁ HI₂); apply inj_pairT2 in HT; subst.
      revert HD0; apply irreflexivity.
    + assert (HT := tctd_det HI₁ HI₂); now inversion HT.
  - inversion HI.
  - inversion HI.
  - inversion HI.
  - inversion HI.
Qed.

#[export] Instance Symm_tdiscr {Δ κ} : Symmetric (λ τ₁ τ₂, @tdiscr Δ (c_eq κ τ₁ τ₂)).
Proof.
  intros τ₁ τ₂ HD; inversion HD; subst;
  repeat match goal with
         | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pairT2 in H
         end; subst; eauto using @tdiscr; [].
  econstructor; [eassumption .. |]; clear -HD0; unfold cdiscrK in *.
  destruct (kindEqDec.eq_dec κ₂ κ₁); [subst; simpl; symmetry | exact I].
  destruct (kindEqDec.eq_dec κ₁ κ₁) as [EQ | NEQ]; [| contradiction].
  now rewrite UIP_refl with (p := EQ) in HD0.
Qed.

Definition tequiv {Δ κ} Ψ (τ₁ τ₂ : typ κ Δ) := tproves_i Ψ (c_eq κ τ₁ τ₂).
Arguments tequiv {_ _} _ _ _ /.

#[export] Instance Equiv_tproves {Δ κ Ψ} : (Equivalence (@tequiv Δ κ Ψ)).
Proof.
  split.
  - intros τ; simpl; induction τ; now eauto using @tproves_i.
  - intros τ₁ τ₂ EQ; simpl in *; now apply tpi_symm.
  - intros τ₁ τ₂ τ₃ EQ₁ EQ₂; simpl in *; eapply tpi_trans; eassumption.
Qed.

Lemma tctd_fmap {Δ Δ' : Ctx kind} κ κ' (τ : typ κ _) (c : tctor κ') (f : Δ [→] Δ')
      (HC : tctd τ c) :
  tctd (fmap f τ) c.
Proof.
  induction HC; term_simpl; eauto using @tctd.
Qed.

Lemma tdiscr_fmap (Δ Δ' : Ctx kind) (ψ : constr Δ) (f : Δ [→] Δ')
      (HC : tdiscr ψ) :
  tdiscr (fmap f ψ).
Proof.
  induction HC; term_simpl; eauto using @tdiscr, tctd_fmap.
Qed.

Lemma tproves_i_map {Δ Δ' : Ctx kind} Ψ φ (f : Δ [→] Δ') (H : Ψ ⊩ φ) :
  map (fmap f) Ψ ⊩ fmap f φ.
Proof.
  generalize dependent Δ'.
  induction H; intros; term_simpl; try (econstructor; now eauto).
  - apply tpi_ax.
    rewrite in_map_iff; eauto.
  - apply tpi_lam.
    erewrite map_map, map_ext, <- map_map; [apply IHtproves_i |].
    intros ψ; now term_simpl.
  - term_simpl in IHtproves_i.
    eapply tpi_appInjR, IHtproves_i; now eauto using tctd_fmap.
  - term_simpl in IHtproves_i.
    eapply tpi_appInjL, IHtproves_i; now eauto using tctd_fmap.
  - term_simpl in IHtproves_i.
    eapply tpi_carrInjR, IHtproves_i; now eauto using tctd_fmap.
  - term_simpl in IHtproves_i.
    eapply tpi_cprodInjR, IHtproves_i; now eauto using tctd_fmap.
  - term_simpl in IHtproves_i1.
    eapply tpi_cprodInjL; now eauto.
  - term_simpl in IHtproves_i1.
    eapply tpi_carrInjL; now eauto.
Qed.

Lemma tctd_bind {Δ Δ' : Ctx kind} κ κ' τ c (f : Δ [⇒] Δ') (H : @tctd Δ κ τ κ' c) :
  tctd (tbind f τ) c.
Proof.
  induction H; term_simpl; now eauto using @tctd.
Qed.

Lemma tproves_i_bind {Δ Δ' : Ctx kind} Ψ φ (f : Δ [⇒] Δ') (H : Ψ ⊩ φ) :
  map (bind f) Ψ ⊩ bind f φ.
Proof.
  generalize dependent Δ'.
  induction H; intros; term_simpl; try (econstructor; now eauto).
  - apply tpi_ax.
    rewrite in_map_iff; eauto.
  - destruct EQ₁; rewrite UIP_refl with (p := EQ₂).
    now change (tequiv (map (bind f) Ψ) (f _ x eq_refl) (f _ x eq_refl)).
  - apply tpi_lam.
    erewrite map_map, map_ext, <- map_map; [apply IHtproves_i |].
    intros ψ; now term_simpl.
  - term_simpl in IHtproves_i.
    eapply tpi_appInjR, IHtproves_i; now eauto using tctd_bind.
  - term_simpl in IHtproves_i.
    eapply tpi_appInjL, IHtproves_i; now eauto using tctd_bind.
  - term_simpl in IHtproves_i.
    eapply tpi_carrInjR, IHtproves_i; now eauto.
  - term_simpl in IHtproves_i.
    eapply tpi_cprodInjR, IHtproves_i; now eauto.
  - term_simpl in IHtproves_i1.
    eapply tpi_cprodInjL; now eauto.
  - term_simpl in IHtproves_i1.
    eapply tpi_carrInjL; now eauto.
Qed.

Lemma tdiscr_bind {Δ Δ' : Ctx kind} φ (f : Δ [⇒] Δ') (H : ⊮ φ) :
  ⊮ bind f φ.
Proof.
  induction H; term_simpl; eauto using @tdiscr, tctd_bind.
Qed.

Lemma tproves_i_constr_weak {Δ} Ψ Ψ₁ Ψ₂ (c : constr Δ)
  (HT : Ψ₁ ++ Ψ₂ ⊩ c) :
  Ψ₁ ++ Ψ ++ Ψ₂ ⊩ c.
Proof.
  remember (Ψ₁ ++ Ψ₂) as Ψ' eqn: EQΨ.
  induction HT; subst; try (econstructor; now eauto); [| |].
  - apply tpi_ax; rewrite !in_app_iff in *; tauto.
  - apply tpi_lam; rewrite !map_app; apply IHHT, map_app.
  - eapply tpi_appInjR, IHHT; eauto.
Qed.

Lemma tproves_i_weak_head {Δ Ψ} {ψ φ : constr Δ}
      (HT : Ψ ⊩ φ) :
  ψ :: Ψ ⊩ φ.
Proof.
  apply tproves_i_constr_weak with (Ψ := _ :: nil) (Ψ₁ := nil), HT.
Qed.

Lemma constr_cut {Δ : Ctx kind} Ψ₁ Ψ₂ Ψ₃ (φ : constr Δ)
      (H1 : ∀ ψ, In ψ Ψ₂ -> Ψ₁ ++ Ψ₃ ⊩ ψ)
      (H2 : Ψ₁ ++ Ψ₂ ++ Ψ₃ ⊩ φ) :
  Ψ₁ ++ Ψ₃ ⊩ φ.
Proof.
  remember (Ψ₁ ++ Ψ₂ ++ Ψ₃) as Ψ eqn: EQΨ; induction H2; subst;
    try (econstructor; now eauto); [| |].
  - rewrite !in_app_iff in HIn; destruct HIn as [HIn | [HIn | HIn]];
      try (apply tpi_ax; rewrite in_app_iff; tauto); [].
    apply H1, HIn.
  - apply tpi_lam; rewrite map_app.
    eapply IHtproves_i; [| now rewrite !map_app].
    intros ψ' HIn; rewrite <- map_app.
    rewrite in_map_iff in HIn; destruct HIn as [ψ [EQ HIn]]; subst ψ'.
    apply tproves_i_map, H1, HIn.
  - eapply tpi_appInjR, IHtproves_i; [eassumption .. | reflexivity].
Qed.

Lemma tproves_i_cut_head {Δ Ψ} {ψ φ : constr Δ}
      (HPψ : Ψ ⊩ ψ)
      (HPφ : ψ :: Ψ ⊩ φ) :
  Ψ ⊩ φ.
Proof.
  eapply constr_cut with (Ψ₁ := nil) (Ψ₂ := _ :: nil), HPφ; simpl.
  intros ψ' [EQ | []]; now subst.
Qed.

Lemma subst_self_eq {Δ κ₁ κ₂} (τ : typ κ₂ (Δ ▹ κ₁)) :
  subst (F := typ κ₁) (fmap (mk_shift ↑)%bind τ) (t_var κ₁ (VZ : dom (Δ ▹ κ₁)) eq_refl) = τ.
Proof.
  unfold subst; rewrite map_to_bind with (t := τ), bind_bind_comp'; apply bind_pure.
  intros κ [| x] []; term_simpl; reflexivity.
Qed.

Lemma tproves_i_lam {Δ κ₁ κ₂} (τ₁ τ₂ : typ κ₂ (Δ ▹ κ₁))
      (HP : tequiv nil (t_lam τ₁) (t_lam τ₂)) :
  tequiv nil τ₁ τ₂.
Proof.
  rewrite <- (subst_self_eq τ₁), <- (subst_self_eq τ₂).
  etransitivity; [| apply tpi_beta].
  etransitivity; [symmetry; apply tpi_beta |].
  apply tpi_app, tpi_var.
  apply tproves_i_map with (f := mk_shift) in HP; term_simpl in HP; exact HP.
Qed.
