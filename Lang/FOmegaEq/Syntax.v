Require Import Utf8.
Require Import Binding.Lib Binding.Set Binding.Auto.
Require Import Lang.FOmegaEq.Kinds Lang.FOmegaEq.Types.
Import DED_kind.

Inductive ax := L | R.

Inductive value {V : Set} :=
| v_var (x : V) : value
| v_unit : value
| v_lam (e : @expr (inc V)) : value
| v_pair (v₁ v₂ : value) : value
| v_inj (a : ax) (v : value) : value
| v_tlam (e : expr) : value
| v_pack (v : value) : value
| v_roll (v : value) : value
| v_lamC  (e : expr) : value
| v_withC (v : value) : value
| v_fix (e : @expr (inc (inc V))) : value
with expr {V : Set} :=
| e_val (v : value) : expr
| e_bind (e₁ : expr) (e₂ : @expr (inc V)) : expr
| e_app (v₁ v₂ : value) : expr
| e_tapp (v : value) : expr
| e_proj (a : ax) (v : value) : expr
| e_abort (v : value) : expr
| e_case (v : value) (e₁ e₂ : @expr (inc V)) : expr
| e_unpack (v : value) (e : @expr (inc V)) : expr
| e_unroll (v : value) : expr
| e_cabort : expr
| e_capp (v : value) : expr
| e_lwith (v : value) (e : @expr (inc V)) : expr.

Arguments value V%bind : clear implicits.
Arguments expr  V%bind : clear implicits.

Declare Scope syn_scope.
Delimit Scope syn_scope with syn.

Coercion e_val : value >-> expr.
Coercion e_app : value >-> Funclass.
Notation "e₁ >>= e₂" := (e_bind e₁ e₂) (at level 45, right associativity) : syn_scope.
Notation "'ƛ' e" := (v_lam e) (at level 60) : syn_scope.
Notation "⟨⟩" := v_unit : syn_scope.
Notation "⟨ v ⟩ᶜ" := (v_withC v) : syn_scope.
Notation "⟨ v₁ , v₂ ⟩" := (v_pair v₁ v₂) : syn_scope.
Notation "'Λ' e" := (v_tlam e) (at level 60) : syn_scope.
Notation "'ƛᶜ' e" := (v_lamC e) (at level 60) : syn_scope.
Notation "'rec' e" := (v_fix e) (at level 60) : syn_scope.

Local Open Scope bind_scope.
Local Open Scope syn_scope.

Fixpoint emap {A B : Set} (f : A [→] B) (e : expr A) : expr B :=
  match e with
  | e_val v => vmap f v
  | e₁ >>= e₂ => emap f e₁ >>= emap (f ↑) e₂
  | e_app v₁ v₂ => (vmap f v₁) (vmap f v₂)
  | e_tapp v => e_tapp (vmap f v)
  | e_proj x v => e_proj x (vmap f v)
  | e_abort v => e_abort (vmap f v)
  | e_case v e₁ e₂ => e_case (vmap f v) (emap (f ↑) e₁) (emap (f ↑) e₂)
  | e_unpack v e => e_unpack (vmap f v) (emap (f ↑) e)
  | e_unroll v => e_unroll (vmap f v)
  | e_cabort => e_cabort
  | e_capp v => e_capp (vmap f v)
  | e_lwith v e => e_lwith (vmap f v) (emap (f ↑) e)
  end
with vmap {A B : Set} (f : A [→] B) (v : value A) : value B :=
       match v with
       | v_var x => v_var (f x)
       | ƛ e => ƛ (emap (f ↑) e)
       | Λ e => Λ (emap f e)
       | ⟨⟩ => ⟨⟩
       | ⟨v₁, v₂⟩ => ⟨vmap f v₁, vmap f v₂⟩
       | v_inj x v => v_inj x (vmap f v)
       | v_pack v => v_pack (vmap f v)
       | v_roll v => v_roll (vmap f v)
       | ƛᶜ e => v_lamC (emap f e)
       | ⟨v⟩ᶜ => ⟨vmap f v⟩ᶜ
       | rec e => rec (emap ((f ↑) ↑) e)
       end.
#[export] Instance FMap_expr : FunctorCore expr := @emap.
#[export] Instance FMap_val  : FunctorCore value := @vmap.

#[export] Instance SPC_val : SetPureCore value := @v_var.
Fixpoint ebind {X Y : Set} (f : X [⇒] Y) (e : expr X) : expr Y :=
  match e with
  | e_val v => vbind f v
  | e₁ >>= e₂ => ebind f e₁ >>= ebind (f ↑) e₂
  | e_app v₁ v₂ => (vbind f v₁) (vbind f v₂)
  | e_tapp v => e_tapp (vbind f v)
  | e_proj x v => e_proj x (vbind f v)
  | e_abort v => e_abort (vbind f v)
  | e_case v e₁ e₂ => e_case (vbind f v) (ebind (f ↑) e₁) (ebind (f ↑) e₂)
  | e_unpack v e => e_unpack (vbind f v) (ebind (f ↑) e)
  | e_unroll v => e_unroll (vbind f v)
  | e_cabort => e_cabort
  | e_capp v => e_capp (vbind f v)
  | e_lwith v e => e_lwith (vbind f v) (ebind (f ↑) e)
  end
with vbind {X Y : Set} (f : X [⇒] Y) (v : value X) : value Y :=
       match v with
       | v_var x => f x
       | ƛ e => ƛ (ebind (f ↑) e)
       | Λ e => Λ (ebind f e)
       | ⟨⟩ => ⟨⟩
       | ⟨v₁, v₂⟩ => ⟨vbind f v₁, vbind f v₂⟩
       | v_inj x v => v_inj x (vbind f v)
       | v_pack v => v_pack (vbind f v)
       | v_roll v => v_roll (vbind f v)
       | ƛᶜ  e => ƛᶜ (ebind f e)
       | ⟨v⟩ᶜ => ⟨vbind f v⟩ᶜ
       | rec e => rec (ebind ((f ↑) ↑) e)
       end.

#[export] Instance BindCore_expr : BindCore expr := @ebind.
#[export] Instance BindCore_val  : BindCore value := @vbind.

#[export] Instance IP_typ : SetPure value.
Proof.
  split; intros; reflexivity.
Qed.

Fixpoint vmap_id X (δ : X [→] X) v : δ ≡ ı → fmap δ v = v
with emap_id X (δ : X [→] X) (e : expr X) : δ ≡ ı → fmap δ e = e.
Proof.
  - auto_map_id.
  - auto_map_id.
Qed.

Fixpoint vmap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (v : value A) :
  f ∘ g ≡ h → fmap f (fmap g v) = fmap h v
with emap_comp (A B C : Set) (f : B [→] C) (g : A [→] B) h (e : expr A) :
  f ∘ g ≡ h → fmap f (fmap g e) = fmap h e.
Proof.
  - auto_map_comp.
  - auto_map_comp.
Qed.

#[export] Instance Functor_val : Functor value.
Proof.
  split; [exact vmap_id | exact vmap_comp].
Qed.
#[export] Instance Functor_expr : Functor expr.
Proof.
  split; [exact emap_id | exact emap_comp].
Qed.

Fixpoint vmap_vbind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (v : value A) :
  f ̂ ≡ g → fmap f v = bind g v
with emap_ebind_pure (A B : Set) (f : A [→] B) (g : A [⇒] B) (e : expr A) :
  f ̂ ≡ g → fmap f e = bind g e.
Proof.
  - auto_map_bind_pure.
    erewrite emap_ebind_pure; [reflexivity |].
    intros [| [| x]]; term_simpl; [reflexivity | reflexivity |].
    rewrite <-(EQ x).
    reflexivity.
  - auto_map_bind_pure.
Qed.

#[export] Instance BindMapPure_val : BindMapPure value.
Proof.
  split; intros; now apply vmap_vbind_pure.
Qed.
#[export] Instance BindMapPure_expr : BindMapPure expr.
Proof.
  split; intros; now apply emap_ebind_pure.
Qed.

Fixpoint vmap_vbind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
         (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (v : value A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ v) = fmap f₁ (bind g₁ v)
with emap_ebind_comm (A B₁ B₂ C : Set) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
                     (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (e : expr A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ e) = fmap f₁ (bind g₁ e).
Proof.
  - auto_map_bind_comm.
    erewrite emap_ebind_comm; [reflexivity |].
    erewrite lift_comm; [reflexivity |].
    erewrite lift_comm; [reflexivity | assumption].
  - auto_map_bind_comm.
Qed.

#[export] Instance BindMapComm_val : BindMapComm value.
Proof.
  split; intros; now apply vmap_vbind_comm.
Qed.
#[export] Instance BindMapComm_expr : BindMapComm expr.
Proof.
  split; intros; now apply emap_ebind_comm.
Qed.

Fixpoint vbind_id (A : Set) (f : A [⇒] A) (v : value A) :
  f ≡ ı → bind f v = v
with ebind_id  (A : Set) (f : A [⇒] A) (e : expr A) :
  f ≡ ı → bind f e = e.
Proof.
  - auto_bind_id.
    rewrite ebind_id; [reflexivity |].
    apply lift_id, lift_id; assumption.
  - auto_bind_id.
Qed.

Fixpoint vbind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (v : value A) :
  f ∘ g ≡ h → bind f (bind g v) = bind h v
with ebind_comp (A B C : Set) (f : B [⇒] C) (g : A [⇒] B) h (e : expr A) :
 f ∘ g ≡ h → bind f (bind g e) = bind h e.
Proof.
  - auto_bind_comp.
    erewrite ebind_comp; [reflexivity |].
    erewrite lift_comp; [reflexivity |].
    erewrite lift_comp; [reflexivity | assumption].
  - auto_bind_comp.
Qed.

#[export] Instance Bind_val : Bind value.
Proof.
  split; intros; [now apply vbind_id | now apply vbind_comp].
Qed.
#[export] Instance Bind_expr : Bind expr.
Proof.
  split; intros; [now apply ebind_id | now apply ebind_comp].
Qed.
