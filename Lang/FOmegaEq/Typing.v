Require Import Utf8.
Require Import Coq.Lists.List.
Require Import Lang.FOmegaEq.Types Lang.FOmegaEq.Kinds Lang.FOmegaEq.Syntax.
Require Import Binding.Lib Binding.Set.
Require Import Binding.Env.
Import Binding.Intrinsic (Ctx, dom, extC, Build_Ctx, mtC).

Reserved Notation "Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ" (at level 70, Ψ, Γ, e at level 60).
Reserved Notation "Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ" (at level 70, Ψ, Γ, v at level 60).

(* The type system (Fig. 5) *)
Inductive typing_expr {V : Set} (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> (typ ⋆ Δ)) :
  expr V -> typ ⋆ Δ -> Prop :=
| T_val {τ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ v : τ
| T_bind  {τ₁ τ₂ e₁ e₂} :
  Δ ∣ Ψ ∣ Γ ⊢ₑ e₁ : τ₁ -> Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e₂ : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e₁ >>= e₂ : τ₂
| T_congE {τ τ' e} : Ψ ⊩ τ ≃ τ' -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ'
| T_app  τ₁ τ₂ v₁ v₂ :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v₁ : τ₁ →ᵗ τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v₂ : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ₑ v₁ v₂ : τ₂
| T_tapp {κ τ σ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : ∀ᵗ κ , τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_tapp v : subst τ σ
| T_projL {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ × τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_proj L v : τ₁
| T_projR {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ × τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_proj R v : τ₂
| T_abort {τ : typ ⋆ Δ} {v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : ⊥ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_abort v : τ
| T_case {τ₁ τ₂ : typ ⋆ Δ} {τ} {v e₁ e₂} :
  Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e₁ : τ -> Δ ∣ Ψ ∣ Γ ▹ τ₂ ⊢ₑ e₂ : τ ->
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ + τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_case v e₁ e₂ : τ
| T_unpack {κ} {τ τ'} {v e} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : ∃ᵗ κ , τ ->
  extC κ Δ ∣ map shift Ψ ∣ shift • Γ ▹ τ ⊢ₑ e : shift τ' ->
  Δ ∣ Ψ ∣ Γ ⊢ₑ e_unpack v e : τ'
| T_unroll κ τ σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂) v :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : σ₁ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_unroll v : σ₂
| T_cabort {τ : typ ⋆ Δ} {ψ}  :
  Ψ ⊩ ψ -> ⊮ ψ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_cabort : τ
| T_capp {φ τ} {v} :
  Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : φ →ᶜ τ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e_capp v : τ
| T_lwith {φ τ} {σ : typ ⋆ Δ} {v e} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : φ ×ᶜ σ -> Δ ∣ φ :: Ψ ∣ Γ ▹ σ ⊢ₑ e : τ ->
  Δ ∣ Ψ ∣ Γ ⊢ₑ e_lwith v e : τ
where "Δ ∣ Ψ ∣ Γ ⊢ₑ e : τ" := (typing_expr Δ Ψ%typ Γ%typ e%syn τ%typ)
with typing_val {V : Set} (Δ : Ctx kind) (Ψ : list (constr Δ)) (Γ : V -> (typ ⋆ Δ)) : value V -> typ ⋆ Δ -> Prop :=
| T_var {x τ} (EQ : Γ x = τ) : Δ ∣ Ψ ∣ Γ ⊢ᵥ v_var x : τ
| T_congV {v τ τ'} : Ψ ⊩ τ ≃ τ' -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ'
| T_unit : Δ ∣ Ψ ∣ Γ ⊢ᵥ ⟨⟩ : ⊤
| T_lam {τ₁ τ₂ e} :
  Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ƛ e : τ₁ →ᵗ τ₂
| T_pair {τ₁ τ₂ v₁ v₂} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v₁ : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v₂ : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ⟨v₁, v₂⟩ : τ₁ × τ₂
| T_injl {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_inj L v : τ₁ + τ₂
| T_injr {τ₁ τ₂ v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_inj R v : τ₁ + τ₂
| T_tlam {κ τ e} :
  extC κ Δ ∣ map shift Ψ ∣ compose shift Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ Λ e : ∀ᵗ κ, τ
| T_pack κ {τ : typ ⋆ (extC κ Δ)} {τ' : typ κ Δ} {v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : subst τ τ' -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_pack v : ∃ᵗ κ, τ
| T_roll κ τ σ₁ σ₂ (HF : rel_app κ (rec_type Δ κ τ) (subst τ (rec_type Δ κ τ)) ⋆ σ₁ σ₂) v :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : σ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ v_roll v : σ₁
| T_lamC {φ τ} {e} :
  Δ ∣ φ :: Ψ ∣ Γ ⊢ₑ e : τ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ƛᶜ e : φ →ᶜ τ
| T_withC {φ τ} {v} :
  Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ -> Ψ ⊩ φ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ ⟨v⟩ᶜ : φ ×ᶜ τ
| T_rec {τ₁ τ₂ : typ ⋆ Δ} {e : expr (inc (inc V))} :
  Δ ∣ Ψ ∣ Γ ▹ (τ₁ →ᵗ τ₂) ▹ τ₁ ⊢ₑ e : τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ᵥ (v_fix e) : τ₁ →ᵗ τ₂
where "Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ" := (typing_val Δ Ψ%typ Γ%typ v%syn τ%typ).

Hint Constructors typing_expr.
Hint Constructors typing_val.

Fixpoint etypes_equiv_ctx {X : Set} {Δ Ψ e τ} {Γ₁ Γ₂ : X → typ ⋆ Δ}
         (EQ : ∀ x : X, tequiv Ψ (Γ₁ x) (Γ₂ x))
         (HT : Δ ∣ Ψ ∣ Γ₁ ⊢ₑ e : τ) :
  Δ ∣ Ψ ∣ Γ₂ ⊢ₑ e : τ
with vtypes_equiv_ctx {X : Set} {Δ Ψ v τ} {Γ₁ Γ₂ : X → typ ⋆ Δ}
         (EQ : ∀ x : X, tequiv Ψ (Γ₁ x) (Γ₂ x))
         (HT : Δ ∣ Ψ ∣ Γ₁ ⊢ᵥ v : τ) :
  Δ ∣ Ψ ∣ Γ₂ ⊢ᵥ v : τ.
Proof.
  - destruct HT; try (econstructor; now eauto); [| | |].
    + eapply T_bind; [now eauto | eapply etypes_equiv_ctx, HT2].
      intros [| x]; [reflexivity | apply EQ].
    + eapply T_case; [eapply etypes_equiv_ctx; [| eassumption] .. | now eauto ];
        (intros [| x]; [reflexivity | apply EQ]).
    + eapply T_unpack; [now eauto | eapply etypes_equiv_ctx, HT].
      intros [| x]; [reflexivity | simpl].
      apply tproves_i_map with (φ := c_eq ⋆ _ _), EQ.
    + eapply T_lwith; [now eauto | eapply etypes_equiv_ctx, HT].
      intros [| x]; [reflexivity | simpl].
      apply tproves_i_weak_head, EQ.
  - destruct HT; try (econstructor; now eauto); [| | | |].
    + subst; eapply T_congV, T_var; [apply tpi_symm, EQ | reflexivity].
    + eapply T_lam, etypes_equiv_ctx, H.
      intros [| x]; [reflexivity | apply EQ].
    + eapply T_tlam, etypes_equiv_ctx, H.
      intros x; apply tproves_i_map with (φ := c_eq ⋆ _ _), EQ.
    + eapply T_lamC, etypes_equiv_ctx, H.
      intros x; apply tproves_i_weak_head, EQ.
    + eapply T_rec, etypes_equiv_ctx, H.
      intros [| [| x]]; [reflexivity | reflexivity | apply EQ].
Qed.

Lemma typing_expr_fmap {V₁ V₂ : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
  (Γ₁ : V₁ -> typ ⋆ Δ) (Γ₂ : V₂ -> typ ⋆ Δ)
  (e : expr V₁) (τ : typ ⋆ Δ)
  (δ : V₁ [→] V₂)
  (EQ : Γ₁ ≡ Γ₂ • δ)
  (HT : Δ ∣ Ψ ∣ Γ₁ ⊢ₑ e : τ)
  : typing_expr Δ Ψ Γ₂ (fmap δ e) τ
with
typing_val_fmap {V₁ V₂ : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)}
  (Γ₁ : V₁ -> (typ ⋆ Δ)) (Γ₂ : V₂ -> (typ ⋆ Δ))
  (v : value V₁) (τ : typ ⋆ Δ)
  (δ : V₁ [→] V₂)
  (EQ : Γ₁ ≡ Γ₂ • δ)
  (HT : typing_val Δ Ψ Γ₁ v τ)
  : typing_val Δ Ψ Γ₂ (fmap δ v) τ.
Proof.
  - destruct HT; term_simpl; try (econstructor; now eauto); [| | |].
    + eapply T_bind; [now eauto |].
      eapply typing_expr_fmap, HT2; solve_equiv.
    + eapply T_case; [.. | now eauto].
      * eapply typing_expr_fmap, HT1; solve_equiv.
      * eapply typing_expr_fmap, HT2; solve_equiv.
    + eapply T_unpack; [now eauto |].
      eapply typing_expr_fmap, HT; solve_equiv.
    + eapply T_lwith; [now eauto |].
      eapply typing_expr_fmap, HT; solve_equiv.
  - destruct HT; term_simpl; try (econstructor; now eauto); [| | |].
    + subst; apply T_var.
      symmetry; apply EQ.
    + eapply T_lam, typing_expr_fmap, H; solve_equiv.
    + eapply T_tlam, typing_expr_fmap, H; solve_equiv.
    + eapply T_rec, typing_expr_fmap, H; solve_equiv.
Qed.

Lemma typing_shift_exp {V : Set} Δ (Ξ : list (constr Δ)) Γ τ τ' e (HT : typing_expr Δ Ξ Γ e τ) : typing_expr Δ Ξ (Γ ▹ τ') (shift (A := V) e) τ.
Proof.
  apply typing_expr_fmap with Γ; [| assumption].
  solve_equiv.
Qed.

Lemma typing_shift_val {V : Set} Δ (Ξ : list (constr Δ)) Γ τ τ' v (HT : typing_val Δ Ξ Γ v τ) : typing_val Δ Ξ (Γ ▹ τ') (shift (A := V) v) τ.
Proof.
  apply typing_val_fmap with Γ; [| assumption].
  solve_equiv.
Qed.

Lemma typing_expr_constr_weak {V Δ Γ e τ} Ψ Ψ₁ Ψ₂
  (HT : @typing_expr V Δ (Ψ₁ ++ Ψ₂) Γ e τ)
  : @typing_expr V Δ (Ψ₁ ++ Ψ ++ Ψ₂) Γ e τ
with typing_val_constr_weak {V Δ Γ v τ} Ψ Ψ₁ Ψ₂
       (HT : @typing_val V Δ (Ψ₁ ++ Ψ₂) Γ v τ)
  : @typing_val V Δ (Ψ₁ ++ Ψ ++ Ψ₂) Γ v τ.
Proof.
  - destruct HT; try (econstructor; now eauto using tproves_i_constr_weak); [|].
    + eapply T_unpack; [now eauto |].
      rewrite !map_app in *; now eauto.
    + eapply T_lwith; [now eauto |].
      eapply typing_expr_constr_weak with (Ψ₁ := _ :: _), HT.
  - destruct HT; try (econstructor; now eauto using tproves_i_constr_weak); [|].
    + apply T_tlam.
      rewrite !map_app in *; now eauto.
    + eapply T_lamC, typing_expr_constr_weak with (Ψ₁ := _ :: _), H.
Qed.

Lemma vtypes_weak_head {V Δ ψ Ψ Γ v τ}
      (HT : @typing_val V Δ Ψ Γ v τ) :
  typing_val Δ (ψ :: Ψ) Γ v τ.
Proof.
  now apply typing_val_constr_weak with (Ψ₁ := nil) (Ψ := _ :: nil).
Qed.

Lemma typing_expr_ctx_extensional_eq {V : Set} {Δ Ξ} {Γ₁ Γ₂ : V -> typ ⋆ Δ} {e τ}
  (ρ : Γ₁ ≡ Γ₂)
  (HT : typing_expr Δ Ξ Γ₁ e τ)
  : typing_expr Δ Ξ Γ₂ e τ.
Proof.
  eapply etypes_equiv_ctx, HT.
  intros x; now rewrite (ρ x).
Qed.

Lemma typing_val_ctx_extensional_eq {V : Set} {Δ Ξ} {Γ₁ Γ₂ : V -> typ ⋆ Δ} {v τ}
       (ρ : Γ₁ ≡ Γ₂)
       (HT : typing_val Δ Ξ Γ₁ v τ)
  : typing_val Δ Ξ Γ₂ v τ.
Proof.
  eapply vtypes_equiv_ctx, HT.
  intros x; now rewrite (ρ x).
Qed.

Lemma rel_app_map {Δ Δ'} {κ κ'}
  (τ₁ τ₂ : typ κ Δ) (σ₁ σ₂ : typ κ' Δ)
  (f : Intrinsic.Arr Δ Δ')
  (HF : rel_app κ τ₁ τ₂ κ' σ₁ σ₂)
  : rel_app κ (fmap f τ₁) (fmap f τ₂) κ' (fmap f σ₁) (fmap f σ₂).
Proof.
  induction HF; term_simpl; eauto using @rel_app.
Qed.

Lemma rel_app_bind {Δ Δ'} {κ κ'}
  (τ₁ τ₂ : typ κ Δ) (σ₁ σ₂ : typ κ' Δ)
  (f : Intrinsic.Sub Δ Δ')
  (HF : rel_app κ τ₁ τ₂ κ' σ₁ σ₂)
  : rel_app κ (bind f τ₁) (bind f τ₂) κ' (bind f σ₁) (bind f σ₂).
Proof.
  induction HF; term_simpl; eauto using @rel_app.
Qed.

Lemma rel_app_tproves_i {Δ : Ctx kind} {κ₁ κ₂} τ₁ τ₂ (σ₁ σ₂ : typ _ Δ) (HF : rel_app κ₁ τ₁ τ₂ κ₂ σ₁ σ₂)
  (T : nil ⊩ τ₁ ≃ τ₂)
  : nil ⊩ σ₁ ≃ σ₂.
Proof.
  induction HF.
  - assumption.
  - apply tpi_app.
    apply IHHF.
    apply Equiv_tproves.
Qed.

Lemma typing_expr_fmap_types {V : Set} {Δ Δ' Ξ} {Γ : V -> typ ⋆ Δ} {e τ}
  (f : Binding.Intrinsic.Arr Δ Δ')
  (HT : Δ ∣ Ξ ∣ Γ ⊢ₑ e : τ)
  : Δ' ∣ map (fmap f) Ξ ∣ fmap f • Γ ⊢ₑ e : fmap f τ
with typing_val_fmap_types {V : Set} {Δ Δ' Ξ} {Γ : V -> typ ⋆ Δ} {v τ}
       (f : Binding.Intrinsic.Arr Δ Δ')
       (HT : Δ ∣ Ξ ∣ Γ ⊢ᵥ v : τ)
  : Δ' ∣ map (fmap f) Ξ ∣ fmap f • Γ ⊢ᵥ v : fmap f τ.
Proof.
  - destruct HT; term_simpl.
    + apply T_val.
      apply typing_val_fmap_types; assumption.
    + apply T_bind with (tmap f τ₁); [now eauto |].
      eapply typing_expr_ctx_extensional_eq, typing_expr_fmap_types, HT2; solve_equiv.
    + apply T_congE with (tmap f τ), typing_expr_fmap_types, HT.
      now apply tproves_i_map with (φ := c_eq _ _ _).
    + apply T_app with (tmap f τ₁), typing_val_fmap_types, H0.
      now apply typing_val_fmap_types with (τ := t_arr _ _).
    + apply T_tapp, typing_val_fmap_types with (τ := t_all κ _), H.
    + apply T_projL with (tmap f τ₂), typing_val_fmap_types with (τ := t_prod _ _), H.
    + apply T_projR with (tmap f τ₁), typing_val_fmap_types with (τ := t_prod _ _), H.
    + apply T_abort, typing_val_fmap_types with (τ := t_ctor _), H.
    + apply T_case with (tmap f τ₁) (tmap f τ₂), typing_val_fmap_types with (τ := t_sum _ _), H.
      * eapply typing_expr_ctx_extensional_eq, typing_expr_fmap_types, HT1; solve_equiv.
      * eapply typing_expr_ctx_extensional_eq, typing_expr_fmap_types, HT2; solve_equiv.
    + apply T_unpack with κ (tmap (f ↑)%bind τ);
        [apply typing_val_fmap_types with (τ := t_xist κ _), H |].
      apply typing_expr_fmap_types with (f := f ↑ %bind) in HT; term_simpl in HT.
      erewrite map_map, map_ext, <- map_map; [eapply typing_expr_ctx_extensional_eq, HT |].
      * solve_equiv.
      * intros ψ; now term_simpl.
    + apply rel_app_map with (f := f) in HF; term_simpl in HF.
      eapply T_unroll, typing_val_fmap_types, H; eassumption.
    + eapply T_cabort; [now apply tproves_i_map, H | now apply tdiscr_fmap].
    + apply T_capp with (cmap f φ), typing_val_fmap_types with (τ := t_carr _ _), H0.
      apply tproves_i_map; assumption.
    + apply T_lwith with (cmap f φ) (tmap f σ).
      * apply typing_val_fmap_types with (τ := t_cprod _ _), H.
      * eapply typing_expr_ctx_extensional_eq, typing_expr_fmap_types with (Ξ := _ :: _), HT.
        solve_equiv.
  - destruct HT; term_simpl; try (econstructor; now eauto).
    + subst; now apply T_var.
    + apply T_congV with (tmap f τ), typing_val_fmap_types, HT.
      now apply tproves_i_map with (φ := c_eq _ _ _).
    + eapply T_lam, typing_expr_ctx_extensional_eq, typing_expr_fmap_types, H.
      solve_equiv.
    + apply typing_expr_fmap_types with (f := f ↑%bind) in H; term_simpl in H.
      eapply T_tlam.
      erewrite map_map, map_ext, <- map_map; [eapply typing_expr_ctx_extensional_eq, H |].
      * solve_equiv.
      * intros ψ; now term_simpl.
    + apply typing_val_fmap_types with (f := f) in HT; term_simpl in HT.
      eapply T_pack, HT.
    + apply rel_app_map with (f := f) in HF; term_simpl in HF.
      eapply T_roll, typing_val_fmap_types, HT; eassumption.
    + now apply T_lamC, typing_expr_fmap_types with (Ξ := _ :: _).
    + apply T_withC, tproves_i_map, H.
      now apply typing_val_fmap_types.
    + apply T_rec.
      apply (typing_expr_fmap_types _ _ Δ' _ _ _ _ f) in H.
      term_simpl in H.
      eapply typing_expr_ctx_extensional_eq; [| apply H].
      intros [| [| x]]; term_simpl; reflexivity.
Qed.

Lemma typing_expr_bind_types {V : Set} {Δ Δ' Ξ} {Γ : V -> typ ⋆ Δ} {e τ}
  (f : Binding.Intrinsic.Sub Δ Δ')
  (HT : Δ ∣ Ξ ∣ Γ ⊢ₑ e : τ)
  : Δ' ∣ map (bind f) Ξ ∣ bind f • Γ ⊢ₑ e : bind f τ
with typing_val_bind_types {V : Set} {Δ Δ' Ξ} {Γ : V -> typ ⋆ Δ} {v τ}
       (f : Binding.Intrinsic.Sub Δ Δ')
       (HT : Δ ∣ Ξ ∣ Γ ⊢ᵥ v : τ)
  : Δ' ∣ map (bind f) Ξ ∣ bind f • Γ ⊢ᵥ v : bind f τ.
Proof.
  - destruct HT; term_simpl.
    + now apply T_val, typing_val_bind_types.
    + eapply T_bind; [now eauto |].
      eapply typing_expr_ctx_extensional_eq, typing_expr_bind_types, HT2; solve_equiv.
    + eapply T_congE, typing_expr_bind_types, HT.
      now apply tproves_i_bind with (φ := c_eq _ _ _).
    + eapply T_app; [| now eauto].
      now apply typing_val_bind_types with (τ := t_arr τ₁ τ₂).
    + now apply T_tapp, typing_val_bind_types with (τ := t_all κ τ).
    + now eapply T_projL, typing_val_bind_types with (τ := t_prod τ₁ τ₂).
    + now eapply T_projR, typing_val_bind_types with (τ := t_prod τ₁ τ₂).
    + now apply T_abort, typing_val_bind_types with (τ := t_ctor _).
    + eapply T_case, typing_val_bind_types with (τ := t_sum τ₁ τ₂), H; term_simpl.
      * eapply typing_expr_ctx_extensional_eq, typing_expr_bind_types, HT1; solve_equiv.
      * eapply typing_expr_ctx_extensional_eq, typing_expr_bind_types, HT2; solve_equiv.
    + eapply T_unpack; [apply typing_val_bind_types with (τ := t_xist κ τ), H |]; term_simpl.
      eapply typing_expr_bind_types with (f := f ↑ %bind) in HT; term_simpl in HT.
      erewrite map_map, map_ext, <-map_map; [eapply typing_expr_ctx_extensional_eq, HT |].
      * solve_equiv.
      * intros ψ; now term_simpl.
    + eapply T_unroll, typing_val_bind_types, H.
      eapply rel_app_bind with (f := f) in HF; term_simpl in HF; exact HF.
    + eapply T_cabort; [now eapply tproves_i_bind, H |].
      now apply tdiscr_bind.
    + eapply T_capp, typing_val_bind_types with (τ := t_carr _ _), H0; term_simpl.
      now apply tproves_i_bind.
    + eapply T_lwith; [eapply typing_val_bind_types with (τ := t_cprod _ _), H |]; term_simpl.
      eapply typing_expr_ctx_extensional_eq, typing_expr_bind_types with (Ξ := _ :: _), HT.
      solve_equiv.
  - destruct HT; term_simpl; try (econstructor; now eauto).
    + subst; now apply T_var.
    + eapply T_congV, typing_val_bind_types, HT.
      now apply tproves_i_bind with (φ := c_eq _ _ _).
    + eapply T_lam, typing_expr_ctx_extensional_eq, typing_expr_bind_types, H.
      solve_equiv.
    + eapply T_tlam.
      erewrite map_map, map_ext, <- map_map;
        [eapply typing_expr_ctx_extensional_eq, typing_expr_bind_types, H |].
      * solve_equiv.
      * intros ψ; now term_simpl.
    + apply typing_val_bind_types with (f := f) in HT; term_simpl in HT.
      eapply T_pack, HT.
    + eapply rel_app_bind with (f := f) in HF; term_simpl in HF.
      eapply T_roll, typing_val_bind_types, HT; eassumption.
    + now apply T_lamC, typing_expr_bind_types with (Ξ := _ :: _).
    + apply T_withC, tproves_i_bind, H.
      now eapply typing_val_bind_types.
    + apply T_rec.
      apply (typing_expr_bind_types _ _ Δ' _ _ _ _ f) in H.
      term_simpl in H.
      eapply typing_expr_ctx_extensional_eq; [| apply H].
      intros [| [| x]]; term_simpl; reflexivity.
Qed.

Lemma val_typing_sound {V : Set} {Δ : Ctx kind} {Ψ : list (constr Δ)} (Γ : V -> (typ ⋆ Δ)) (v : value V) (τ : typ ⋆ Δ)
  (HT : Δ ∣ Ψ ∣ Γ ⊢ₑ v : τ)
  : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ.
Proof.
  remember (e_val v) as e eqn: EQe; induction HT; inversion EQe; subst; [|].
  - assumption.
  - apply T_congV with τ; [assumption |].
    apply IHHT; reflexivity.
Qed.

Lemma typing_exp_bind {V₁ V₂ : Set} {Δ : Ctx kind} {Ξ : list (constr Δ)}
      (Γ₁ : V₁ -> typ ⋆ Δ) (Γ₂ : V₂ -> typ ⋆ Δ) τ
      (e : expr V₁) (HT : Δ ∣ Ξ ∣ Γ₁ ⊢ₑ e : τ) :
  ∀ (ρ : V₁ [⇒] V₂) (Hρ : ∀ (x : V₁), Δ ∣ Ξ ∣ Γ₂ ⊢ᵥ ρ x : Γ₁ x),
    Δ ∣ Ξ ∣ Γ₂ ⊢ₑ bind ρ e : τ
with typing_val_bind {V₁ V₂ : Set} {Δ : Ctx kind} {Ξ : list (constr Δ)}
                     (Γ₁ : V₁ -> typ ⋆ Δ) (Γ₂ : V₂ -> typ ⋆ Δ) τ
                     (v : value V₁) (HT : Δ ∣ Ξ ∣ Γ₁ ⊢ᵥ v : τ) :
       ∀ (ρ : V₁ [⇒] V₂) (Hρ : ∀ (x : V₁), Δ ∣ Ξ ∣ Γ₂ ⊢ᵥ ρ x : Γ₁ x),
         Δ ∣ Ξ ∣ Γ₂ ⊢ᵥ bind ρ v : τ.
Proof.
  - destruct HT; intros; term_simpl; try (econstructor; now eauto); [| | |].
    + eapply T_bind, typing_exp_bind; [now eauto | eassumption |].
      intros [| x]; term_simpl; [now apply T_var | now apply typing_shift_val].
    + eapply T_case; [eapply typing_exp_bind; [eassumption |] .. | now eauto].
      * intros [| x]; term_simpl; [now apply T_var | now apply typing_shift_val].
      * intros [| x]; term_simpl; [now apply T_var | now apply typing_shift_val].
    + eapply T_unpack; [now eauto | eapply typing_exp_bind; [eassumption |]].
      intros [| x]; term_simpl; [now apply T_var |].
      now apply typing_shift_val, typing_val_fmap_types.
    + eapply T_lwith; [now eauto | eapply typing_exp_bind; [eassumption |]].
      intros [| x]; term_simpl; [now apply T_var | now apply typing_shift_val, vtypes_weak_head].
  - destruct HT; intros; term_simpl; try (econstructor; now eauto using vtypes_weak_head); [| | |].
    + subst; apply Hρ.
    + eapply T_lam, typing_exp_bind; [eassumption |].
      intros [| x]; term_simpl; [now apply T_var | now apply typing_shift_val].
    + eapply T_tlam, typing_exp_bind; [eassumption |].
      intros x; term_simpl; apply typing_val_fmap_types, Hρ.
    + eapply T_rec, typing_exp_bind; [eassumption |].
      intros [| [| x]]; term_simpl; [now apply T_var | now apply T_var |].
      apply typing_shift_val, typing_shift_val, Hρ.
Qed.

Lemma typing_expr_subst {V Δ Ψ Γ v τ₁ τ₂} {e : expr (inc V)}
  (HT₁ : Δ ∣ Ψ ∣ Γ ⊢ᵥ v : τ₁)
  (HT₂ : Δ ∣ Ψ ∣ Γ ▹ τ₁ ⊢ₑ e : τ₂)
  : Δ ∣ Ψ ∣ Γ ⊢ₑ subst e v : τ₂.
Proof.
  apply typing_exp_bind with (Γ ▹ τ₁); [assumption |].
  intros [| x]; term_simpl; [apply HT₁ | now apply T_var].
Qed.

Lemma constr_cut_expr {V Δ Ψ₁ Ψ₂ Ψ₃ Γ τ} {e : expr V}
  (H : ∀ φ, In φ Ψ₂ -> Ψ₁ ++ Ψ₃ ⊩ φ)
  (HT : Δ ∣ Ψ₁ ++ Ψ₂ ++ Ψ₃ ∣ Γ ⊢ₑ e : τ)
  : Δ ∣ Ψ₁ ++ Ψ₃ ∣ Γ ⊢ₑ e : τ
with constr_cut_val {V Δ Ψ₁ Ψ₂ Ψ₃ Γ τ} {v : value V}
       (H : ∀ φ, In φ Ψ₂ -> tproves_i (Ψ₁ ++ Ψ₃) φ)
       (HT : Δ ∣ Ψ₁ ++ Ψ₂ ++ Ψ₃ ∣ Γ ⊢ᵥ v : τ)
  : Δ ∣ Ψ₁ ++ Ψ₃ ∣ Γ ⊢ᵥ v : τ.
Proof.
  - destruct HT; try (econstructor; now eauto using constr_cut); [|].
    + eapply T_unpack; [now eauto |].
      rewrite !map_app in *; eapply constr_cut_expr, HT.
      intros ψ' HIn; rewrite in_map_iff in HIn; destruct HIn as [ψ [EQ HIn]]; subst ψ'.
      rewrite <- map_app; now eauto using tproves_i_map.
    + eapply T_lwith; [now eauto |].
      eapply constr_cut_expr with (Ψ₁ := _ :: _), HT.
      intros ψ HIn; simpl; now eauto using tproves_i_weak_head.
  - destruct HT; try (econstructor; now eauto using constr_cut); [|].
    + apply T_tlam; rewrite !map_app in *.
      eapply constr_cut_expr, H0.
      intros ψ' HIn; rewrite in_map_iff in HIn; destruct HIn as [ψ [EQ HIn]]; subst ψ'.
      rewrite <- map_app; now eauto using tproves_i_map.
    + eapply T_lamC, constr_cut_expr with (Ψ₁ := _ :: _), H0.
      intros ψ HIn; simpl; now eauto using tproves_i_weak_head.
Qed.

(** We can construct a closed term of empty type without using recursive types *)
Section ExampleClosedVoid.

  (* α :: ⋆ ⇒ ⋆, β :: ⋆ ⊢ α β → ⊥ :: ⋆ *)
  Definition ntarr : typ ⋆ (extC (⋆ ⇒ ⋆) (extC ⋆ mtC)) :=
    (0ᵛ (t_var _ (VS VZ : dom (extC _ (extC _ _))) eq_refl) →ᵗ ⊥)%typ.

  (* α :: ⋆ ⇒ ⋆, β :: ⋆ ⊢ (∀ β :: ⋆, α β) ≃ β constr*)
  Definition eqA : constr (extC (⋆ ⇒ ⋆) (extC ⋆ mtC)) :=
    (tc_all ⋆ 0ᵛ ≃ t_var _ (VS VZ : dom (extC _ (extC _ _))) eq_refl)%typ.

  Arguments ntarr : simpl never.
  Arguments eqA : simpl never.

  (* β :: ⋆ ⊢ ∃ α :: ⋆ ⇒ ⋆, ((∀ β :: ⋆, α β) ≃ β) × (α β → ⊥)  :: ⋆ *)
  Definition tloop : typ ⋆ (extC ⋆ mtC) :=
    (∃ᵗ ⋆ ⇒ ⋆, eqA ×ᶜ ntarr)%typ.

  (* ⊢ ∀ β :: ⋆, tloop β :: ⋆ *)
  Definition ltl := (∀ᵗ ⋆, tloop)%typ.

  (* λ x, let *, •, x = x in x ( *, •, x) *)
  Definition foo : value ∅ :=
    v_lam (e_unpack (v_var VZ)
             (e_lwith (v_var VZ)
                (e_app (v_var VZ) (v_pack (v_withC (v_var VZ)))))).

  (*Definition foo : value ∅ :=
  v_lam (e_unpack (v_var VZ)
           (e_lwith (v_var VZ)
              (e_app (v_var VZ) (v_var (VS (VS VZ)))))).
   *)

  Definition nt : expr ∅ := e_app foo (v_pack (v_withC foo)).


  Definition δε {Δ : Ctx kind} : Intrinsic.Arr mtC Δ := {| Intrinsic.apply_arr (x : dom mtC) := match x with end;
                                                          Intrinsic.arr_hom (x : dom mtC) := match x with end |}.

  Lemma δε_unique {Δ : Ctx kind} (δ : Intrinsic.Arr mtC Δ) :
    (δ ≡ δε)%bind.
  Proof.
    intros [].
  Qed.

  Lemma repack {X : Set} {Δ Ψ Γ} (v : value X) :
    Δ ∣ Ψ ∣ Γ ⊢ᵥ v : fmap δε (subst (F := typ ⋆) tloop ltl →ᵗ ⊥) →
                     Δ ∣ Ψ ∣ Γ ⊢ᵥ v_pack ⟨ v ⟩ᶜ : fmap δε (subst (F := typ ⋆) tloop ltl).
  Proof.
    intros HT; rewrite fmap_subst.
    eapply T_pack with (τ' := fmap δε (t_lam tloop)); term_simpl.
    apply T_withC.
    - eapply T_congV, HT; term_simpl.
      apply tpi_app; [| apply tpi_ctor].
      apply tpi_app; [apply tpi_ctor |].
      apply tpi_symm; eapply tpi_trans; [apply tpi_beta |]; term_simpl.
      match goal with
        |- tproves_i ?Δ (c_eq _ ?τ₁ ?τ₂) => change (tequiv Δ τ₁ τ₂)
      end.
      reflexivity.
    - match goal with
        |- tproves_i ?Δ (c_eq _ ?τ₁ ?τ₂) => change (tequiv Δ τ₁ τ₂)
      end.
      reflexivity.
  Qed.

  Lemma tfoo : mtC ∣ nil ∣ □ ⊢ᵥ foo : subst (F := typ ⋆) tloop ltl →ᵗ ⊥.
  Proof.
    eapply T_lam, T_unpack
      with (κ := ⋆ ⇒ ⋆)
           (τ := t_cprod (bind (mk_subst (F := typ ⋆) ltl ↑)%bind eqA)
                   (bind (mk_subst (F := typ ⋆) ltl ↑%bind) ntarr)).
    - eapply T_congV, T_var; [| reflexivity]; term_simpl.
      match goal with
        |- tproves_i ?Δ (c_eq _ ?τ₁ ?τ₂) => change (tequiv Δ τ₁ τ₂)
      end.
      reflexivity.
    - eapply T_lwith; [now apply T_var |].
      assert (HH : typing_val (extC (⋆ ⇒ ⋆) mtC) (bind (mk_subst (F := typ ⋆) ltl ↑)%bind eqA :: nil)
                     (shift • (□ ▹ subst (F := typ ⋆) tloop ltl)
                        ▹ (t_cprod (bind (mk_subst (F := typ ⋆) ltl ↑)%bind eqA)
                             (bind (mk_subst (F := typ ⋆) ltl ↑)%bind ntarr))
                        ▹ bind (mk_subst (F := typ ⋆) ltl ↑)%bind ntarr)
                     (v_var VZ)
                     (t_arr (shift (F := typ ⋆) (subst (F := typ ⋆) tloop ltl)) (t_ctor tc_void))).
      { eapply T_congV, T_var; [| reflexivity]; simpl.
        apply tpi_app, tpi_ctor.
        apply tpi_app; [apply tpi_ctor |]; simpl.
        eapply tpi_trans; [|].
        - eapply tpi_app;
            [| match goal with
                 |- tproves_i ?Δ (c_eq _ ?τ₁ ?τ₂) => change (tequiv Δ τ₁ τ₂); reflexivity
               end].
          unfold eqA; term_simpl.
          eapply tpi_appInjR, tpi_ax; [| | now left]; constructor.
        - eapply tpi_trans; [apply tpi_beta |]; term_simpl.
          match goal with
            |- tproves_i ?Δ (c_eq _ ?τ₁ ?τ₂) => change (tequiv Δ τ₁ τ₂); reflexivity
          end.
      }
      eapply T_app; [exact HH |].
      unfold shift at 3; rewrite δε_unique.
      apply repack; rewrite <- δε_unique with (δ := mk_shift).
      apply HH.
  Qed.

  (* Closed term of the empty type *)
  Lemma tnt : mtC ∣ nil ∣ □ ⊢ₑ nt : ⊥.
  Proof.
    unfold nt; eapply T_app; [apply tfoo |].
    rewrite <- map_id', δε_unique.
    apply repack.
    rewrite <- δε_unique with (δ := ı%bind), map_id'.
    apply tfoo.
  Qed.

End ExampleClosedVoid.
