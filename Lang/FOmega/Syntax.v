Require Import Utf8.
Require Import Binding.Lib Binding.Set.

(** Term-level syntax and the type system of System Fω *)
  
Inductive ax := L | R.

Inductive expr {X : Set} : Set :=
| e_ret (v : value) : expr
| e_let (e₁ : expr) (e₂ : @expr (inc X)) : expr
| e_app (v₁ v₂ : value) : expr
| e_proj (a : ax) (v : value) : expr
| e_abort (v : value) : expr
| e_case (v : value) (e₁ e₂ : @expr (inc X)) : expr
| e_tapp (v : value) : expr
| e_unpack (v : value) (e : @expr (inc X)) : expr
with value {X : Set} : Set :=
| v_var (x : X) : value
| v_lam (e : @expr (inc X)) : value
| v_unit : value
| v_pair (v₁ v₂ : value) : value
| v_inj (a : ax) (v : value) : value
| v_tlam (e : expr) : value
| v_pack (v : value) : value
.
Arguments expr  X : clear implicits.
Arguments value X : clear implicits.
Local Open Scope bind_scope.

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | e_ret v => e_ret (vmap f v)
  | e_let e₁ e₂ => e_let (emap f e₁) (emap (f ↑) e₂)
  | e_app v₁ v₂ => e_app (vmap f v₁) (vmap f v₂)
  | e_tapp v => e_tapp (vmap f v)
  | e_proj x v => e_proj x (vmap f v)
  | e_abort v => e_abort (vmap f v)
  | e_case v e₁ e₂ => e_case (vmap f v) (emap (f ↑) e₁) (emap (f ↑) e₂)
  | e_unpack v e => e_unpack (vmap f v) (emap (f ↑) e)
  end
with vmap {A B : Set} (f : A [→] B) (v : value A) : value B :=
  match v with
  | v_var x => v_var (f x)
  | v_lam e => v_lam (emap (f ↑) e)
  | v_tlam e => v_tlam (emap f e)
  | v_unit => v_unit
  | v_pair v₁ v₂ => v_pair (vmap f v₁) (vmap f v₂)
  | v_inj x v => v_inj x (vmap f v)
  | v_pack v => v_pack (vmap f v)
  end.
#[export] Instance FMap_expr : FunctorCore expr := @emap.
#[export] Instance FMap_val  : FunctorCore value := @vmap.

#[export] Instance SPC_val : SetPureCore value := @v_var.
Fixpoint ebind {X Y : Set} (f : X [⇒] Y) (e : expr X) : expr Y :=
  match e with
  | e_ret v => e_ret (vbind f v)
  | e_let e₁ e₂ => e_let (ebind f e₁) (ebind (f ↑) e₂)
  | e_app v₁ v₂ => e_app (vbind f v₁) (vbind f v₂)
  | e_tapp v => e_tapp (vbind f v)
  | e_proj x v => e_proj x (vbind f v)
  | e_abort v => e_abort (vbind f v)
  | e_case v e₁ e₂ => e_case (vbind f v) (ebind (f ↑) e₁) (ebind (f ↑) e₂)
  | e_unpack v e => e_unpack (vbind f v) (ebind (f ↑) e)
  end
with vbind {X Y : Set} (f : X [⇒] Y) (v : value X) :=
  match v with
  | v_var x => f x
  | v_lam e => v_lam (ebind (f ↑) e)
  | v_tlam e => v_tlam (ebind f e)
  | v_unit => v_unit
  | v_pair v₁ v₂ => v_pair (vbind f v₁) (vbind f v₂)
  | v_inj x v => v_inj x (vbind f v)
  | v_pack v => v_pack (vbind f v)
  end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.
#[export] Instance BindCore_val  : BindCore value := @vbind.

Require Import Binding.Auto.

Fixpoint emap_id (A : Set) (f : A [→] A) (e : expr A) : f ≡ ı → fmap f e = e
with vmap_id (A : Set) (f : A [→] A) (v : value A) : f ≡ ı → fmap f v = v.
Proof.
  - auto_map_id.
  - auto_map_id.
Qed.

Fixpoint emap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : expr A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e
with vmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (v : value A) :
  f ∘ g ≡ h → fmap f (fmap g v) = fmap h v.
Proof.
  - auto_map_comp.
  - auto_map_comp.
Qed.

Instance Functor_value : Functor value.
Proof.
  split; [exact vmap_id | exact vmap_comp].
Qed.

Instance Functor_expr : Functor expr.
Proof.
  split; [exact emap_id | exact emap_comp].
Qed.

#[export] Instance SP_val : SetPure value.
Proof.
  split; intros; term_simpl; reflexivity.
Qed.

Fixpoint emap_ebind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : expr A) :
  f ̂ ≡ g → fmap f e = bind g e
with vmap_vbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (v : value A) :
  f ̂ ≡ g → fmap f v = bind g v.
Proof.
  - auto_map_bind_pure.
  - auto_map_bind_pure.
Qed.

#[export] Instance BindMapPure_expr : BindMapPure expr.
Proof.
  split; exact emap_ebind_pure.
Qed.

#[export] Instance BindMapPure_val : BindMapPure value.
Proof.
  split; exact vmap_vbind_pure.
Qed.

Fixpoint emap_ebind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁)
         (g₂ : B₂ [⇒] C) (e : expr A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e)
with vmap_vbind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂) (g₁ : A [⇒] B₁)
                     (g₂ : B₂ [⇒] C) (v : value A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ v) = fmap f₁ (bind g₁ v).
Proof.
  - auto_map_bind_comm.
  - auto_map_bind_comm.
Qed.

Instance BindMapComm_expr : BindMapComm expr.
Proof.
  split; exact emap_ebind_comm.
Qed.

Instance BindMapComm_value : BindMapComm value.
Proof.
  split; exact vmap_vbind_comm.
Qed.

Fixpoint ebind_id (A : Set) (f : A [⇒] A) (e : expr A) :
  f ≡ ı → bind f e = e
with vbind_id (A : Set) (f : A [⇒] A) (v : value A) :
  f ≡ ı → bind f v = v.
Proof.
  - auto_bind_id.
  - auto_bind_id.
Qed.

Fixpoint ebind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : expr A) :
  f ∘ g ≡ h → bind f (bind g e) = bind h e
with vbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (v : value A) :
  f ∘ g ≡ h → bind f (bind g v) = bind h v.
Proof.
  - auto_bind_comp.
  - auto_bind_comp.
Qed.

#[export] Instance Bind_expr : Bind expr.
Proof.
  split; [exact ebind_id | exact ebind_comp].
Qed.

#[export] Instance Bind_val : Bind value.
Proof.
  split; [exact vbind_id | exact vbind_comp].
Qed.

Require Import Binding.Intrinsic.
Require Import FOmega.Types.

Definition t_arr  {Δ} (σ τ : typ ⋆ Δ) : typ ⋆ Δ := t_app (t_app (t_const tc_arr)  σ) τ.
Definition t_prod {Δ} (σ τ : typ ⋆ Δ) : typ ⋆ Δ := t_app (t_app (t_const tc_prod) σ) τ.
Definition t_sum  {Δ} (σ τ : typ ⋆ Δ) : typ ⋆ Δ := t_app (t_app (t_const tc_sum)  σ) τ.
Definition t_unit {Δ} : typ ⋆ Δ := t_const tc_unit.
Definition t_void {Δ} : typ ⋆ Δ := t_const tc_void.
Definition t_all  {Δ} κ (τ : typ ⋆ (Δ ▹ κ)) : typ ⋆ Δ := t_app (t_const (tc_all  κ)) (t_lam τ).
Definition t_xist {Δ} κ (τ : typ ⋆ (Δ ▹ κ)) : typ ⋆ Δ := t_app (t_const (tc_xist κ)) (t_lam τ).

Definition maybe {A : Set} {B} (f : ∀ a : A, B (VS a)) (x : B VZ) (o : inc A) : B o :=
  match o with
  | VS a => f a
  | VZ => x
  end.
Definition maybe' {A : Set} {B} (f : A → B) (x : B) : inc A → B := @maybe A (λ _, B) f x.
Require Import Basics.

Inductive etypes {X : Set} (Δ : Ctx kind) (Γ : X → typ ⋆ Δ) : expr X → typ ⋆ Δ → Prop :=
| tp_ret {v τ}
         (HT : vtypes Δ Γ v τ) :
    etypes Δ Γ (e_ret v) τ
| tp_bind {e₁ e₂ τ₁ τ₂}
          (HT₁ : etypes Δ Γ e₁ τ₁)
          (HT₂ : etypes Δ (maybe Γ τ₁) e₂ τ₂) :
    etypes Δ Γ (e_let e₁ e₂) τ₂
| tp_app {v₁ v₂ σ τ}
         (HT₁ : vtypes Δ Γ v₁ (t_arr σ τ))
         (HT₂ : vtypes Δ Γ v₂ σ) :
    etypes Δ Γ (e_app v₁ v₂) τ
| tp_projL {v τ₁ τ₂}
           (HT : vtypes Δ Γ v (t_prod τ₁ τ₂)) :
    etypes Δ Γ (e_proj L v) τ₁
| tp_projR {v τ₁ τ₂}
           (HT : vtypes Δ Γ v (t_prod τ₁ τ₂)) :
    etypes Δ Γ (e_proj R v) τ₂
| tp_abort {v} τ
           (HT : vtypes Δ Γ v t_void) :
    etypes Δ Γ (e_abort v) τ
| tp_case {v e₁ e₂ σ₁ σ₂ τ}
          (HT : vtypes Δ Γ v (t_sum σ₁ σ₂))
          (HT₁ : etypes Δ (maybe Γ σ₁) e₁ τ)
          (HT₂ : etypes Δ (maybe Γ σ₂) e₂ τ) :
    etypes Δ Γ (e_case v e₁ e₂) τ
| tp_tapp {v κ τ} σ
          (HT : vtypes Δ Γ v (t_all κ τ)) :
    etypes Δ Γ (e_tapp v) (subst τ σ)
| tp_unpack {v e κ σ τ}
            (HT₁ : vtypes Δ Γ v (t_xist κ σ))
            (HT₂ : etypes (Δ ▹ κ) (maybe' (compose shift Γ) σ) e (shift τ)) :
    etypes Δ Γ (e_unpack v e) τ
| tp_caste {e τ₁ τ₂}
           (HE : tequiv Δ ⋆ τ₁ τ₂)
           (HT : etypes Δ Γ e τ₁) :
    etypes Δ Γ e τ₂

with vtypes {X : Set} (Δ : Ctx kind) (Γ : X → typ ⋆ Δ) : value X → typ ⋆ Δ → Prop :=
| tp_var {τ} (x : X) (EQ : Γ x = τ) :
    vtypes Δ Γ (v_var x) τ
| tp_lam {e σ τ}
         (HT : etypes Δ (maybe Γ σ) e τ) :
    vtypes Δ Γ (v_lam e) (t_arr σ τ)
| tp_unit : vtypes Δ Γ v_unit t_unit
| tp_pair {v₁ v₂ τ₁ τ₂}
          (HT₁ : vtypes Δ Γ v₁ τ₁)
          (HT₂ : vtypes Δ Γ v₂ τ₂) :
    vtypes Δ Γ (v_pair v₁ v₂) (t_prod τ₁ τ₂)
| tp_injL {v τ₁ τ₂}
          (HT : vtypes Δ Γ v τ₁) :
    vtypes Δ Γ (v_inj L v) (t_sum τ₁ τ₂)
| tp_injR {v τ₁ τ₂}
          (HT : vtypes Δ Γ v τ₂) :
    vtypes Δ Γ (v_inj R v) (t_sum τ₁ τ₂)
| tp_tlam {e κ τ}
          (HT : etypes (Δ ▹ κ) (compose shift Γ) e τ) :
    vtypes Δ Γ (v_tlam e) (t_all κ τ)
| tp_pack {v κ σ τ}
          (HT : vtypes Δ Γ v (subst τ σ)) :
    vtypes Δ Γ (v_pack v) (t_xist κ τ)
| tp_castv {v τ₁ τ₂}
           (HE : tequiv Δ ⋆ τ₁ τ₂)
           (HT : vtypes Δ Γ v τ₁) :
    vtypes Δ Γ v τ₂.
