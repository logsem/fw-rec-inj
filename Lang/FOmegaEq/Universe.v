Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic Binding.Auto.
Require Import FOmegaEq.Kinds FOmegaEq.Presheaves.
Require Import RelationClasses Morphisms Basics.
Require Import List.

Module Type Point.
  Parameter P : Type.
End Point.

Module NF (PM : Point).
  Definition Point := PM.P.

  (* Fig. 12/18. Although we have the neu_rel constructor, we can fall
     back to Fig. 12 by taking the parameter P to be the empty type
  *)
  Inductive neu {Δ : Ctx kind} : kind → Type :=
  | neu_var {κ} (x : dom Δ) (EQ : Δ x = κ) : neu κ
  | neu_app {κₐ κᵣ} (ν : neu (κₐ ⇒ κᵣ)) (μ : nf κₐ) : neu κᵣ
  | neu_ctor {κ} (c : tctor κ) : neu κ
  | neu_carr  (φ : nfc) (μ : nf ⋆) : neu ⋆
  | neu_cprod (φ : nfc) (μ : nf ⋆) : neu ⋆
  | neu_rel (P : Point) : neu ⋆
  with nf {Δ : Ctx kind} : kind → Type :=
  | nf_neu (ν : neu ⋆) : nf ⋆
  | nf_lam {κₐ κᵣ} (μ : @nf (Δ ▹ κₐ) κᵣ) : nf (κₐ ⇒ κᵣ)
  with nfc {Δ : Ctx kind} : Type :=
  | nfc_eq κ (μ₁ μ₂ : nf κ) : nfc.

  Arguments nfc Δ : clear implicits.
  Arguments neu Δ : clear implicits.
  Arguments nf Δ  : clear implicits.
  Definition Neu := flip (@neu).
  Definition Nf  := flip (@nf).

  Declare Scope univ_scope.
  Delimit Scope univ_scope with U.

  Coercion neu_app : neu >-> Funclass.
  Coercion neu_ctor : tctor >-> neu.
  Coercion nf_neu : neu >-> nf.

  Definition allN {Δ} κ (μ : Nf ⋆ (extC κ Δ)) :=
    (tc_all κ) (nf_lam μ).

  Definition xistN {Δ} κ (μ : Nf ⋆ (extC κ Δ)) :=
    (tc_xist κ) (nf_lam μ).

  Definition recN {Δ} κ (μ : Nf κ (extC κ Δ)) :=
    (tc_rec κ) (nf_lam μ).

  Notation "'ƛ' τ" := (nf_lam τ : Nf _ _) (at level 60) : univ_scope.
  Notation "σ →ᵗ τ" := (tc_arr σ τ) (at level 55, right associativity) : univ_scope.
  Notation "τ₁ + τ₂" := (tc_sum τ₁ τ₂) (at level 50, left associativity) : univ_scope.
  Notation "τ₁ × τ₂" := (tc_prod τ₁ τ₂) (at level 40, left associativity) : univ_scope.
  Notation "χ →ᶜ τ" := (neu_carr χ τ) (at level 55, right associativity) : univ_scope.
  Notation "χ ×ᶜ τ" := (neu_cprod χ τ) (at level 40, left associativity) : univ_scope.
  Notation "τ₁ ≃ τ₂" := (nfc_eq _ τ₁ τ₂) (at level 65, no associativity) : univ_scope.
  Notation "∀ᵗ κ , τ" := (allN κ τ) (at level 60) : univ_scope.
  Notation "∃ᵗ κ , τ" := (xistN κ τ) (at level 60) : univ_scope.
  Notation "⊥" := tc_void : univ_scope.
  Notation "⊤" := tc_unit : univ_scope.
  Notation "'0ⁿ'" := (neu_var (VZ : dom (_ ▹ _)) eq_refl).

  Local Open Scope bind_scope.
  Local Open Scope univ_scope.

  Fixpoint neumap {κ : kind} {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (ν : Neu κ Δ₁) : Neu κ Δ₂ :=
    match ν with
    | neu_var x EQ  => neu_var (δ x) (eq_trans (arr_hom δ x) EQ)
    | neu_app ν μ   => (neumap δ ν) (nfmap δ μ)
    | neu_ctor c    => c
    | ψ →ᶜ μ => nfcmap δ ψ →ᶜ nfmap δ μ
    | ψ ×ᶜ μ => nfcmap δ ψ ×ᶜ nfmap δ μ
    | neu_rel p => neu_rel p
    end
  with nfmap {κ : kind} {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (μ : Nf κ Δ₁) : Nf κ Δ₂ :=
         match μ with
         | nf_neu ν => neumap δ ν
         | nf_lam μ => ƛ (nfmap (δ ↑) μ)
         end
  with nfcmap {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (ψ : @nfc Δ₁) : @nfc Δ₂ :=
         match ψ with
         | nfc_eq κ μ₁ μ₂ => nfc_eq κ (nfmap δ μ₁) (nfmap δ μ₂)
         end.

  #[export] Instance FMap_neu {κ} : FunctorCore (Neu κ) := @neumap κ.
  #[export] Instance FMap_nf  {κ} : FunctorCore (Nf  κ) := @nfmap κ.
  #[export] Instance FMap_nfc     : FunctorCore (@nfc) := @nfcmap.
  Arguments FMap_neu {κ} /.
  Arguments FMap_nf {κ} /.

  Lemma neuvar_ext {κ Δ} {x y : dom Δ} (EQx : Δ x = κ) (EQy : Δ y = κ) (EQ : x = y) :
    neu_var x EQx = neu_var y EQy.
  Proof.
    subst y; destruct EQy; now rewrite UIP_refl with (p := EQx).
  Qed.

  Fixpoint neumap_id {κ} Δ (δ : Δ [→] Δ) (ν : Neu κ Δ) : δ ≡ ı → fmap δ ν = ν
  with nfmap_id {κ} Δ (δ : Δ [→] Δ) (μ : Nf κ Δ) : δ ≡ ı → fmap δ μ = μ
  with nfcmap_id Δ (δ : Δ [→] Δ) (φ : nfc Δ) : δ ≡ ı → fmap δ φ = φ.
  Proof.
    - auto_map_id; [].
      apply neuvar_ext, EQ.
    - auto_map_id.
    - auto_map_id.
  Qed.

  Fixpoint neumap_comp {κ} (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (ν : Neu κ A) :
    f ∘ g ≡ h → fmap f (fmap g ν) = fmap h ν
  with nfmap_comp {κ} (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (μ : Nf κ A) :
    f ∘ g ≡ h → fmap f (fmap g μ) = fmap h μ
  with nfcmap_comp (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (φ : nfc A) :
    f ∘ g ≡ h → fmap f (fmap g φ) = fmap h φ.
  Proof.
    - auto_map_comp; [].
      apply neuvar_ext, EQ.
    - auto_map_comp.
    - auto_map_comp.
  Qed.

  #[export] Instance Functor_neu {κ} : Functor (Neu κ).
  Proof.
    split; [exact neumap_id | exact neumap_comp].
  Qed.
  #[export] Instance Functor_nf {κ} : Functor (Nf κ).
  Proof.
    split; [exact nfmap_id | exact nfmap_comp].
  Qed.
  #[export] Instance Functor_constr : Functor nfc.
  Proof.
    split; [exact nfcmap_id | exact nfcmap_comp].
  Qed.

  
  Definition PNeu κ : PShf (Ctx kind) (Arr := Arr) :=
    {| FO := Neu κ ;
      Peq := λ A, @eq (Neu κ A);
      Pequiv := λ A, _
    |}.

  Definition PNf κ : PShf (Ctx kind) (Arr := Arr) :=
    {| FO := Nf κ ;
      Peq A := @eq (Nf κ A);
      Pequiv A := _ |}.

  (* Definition 5.2 *)
  Fixpoint kint (κ : kind) : PShf (Ctx kind) (Arr := Arr) :=
    match κ with
    | ⋆ => PNeu ⋆
    | κ₁ ⇒ κ₂ => PArr (kint κ₁) (kint κ₂)
    end.

  Definition PNfc : PShf (Ctx kind) (Arr := Arr) :=
    {| FO := nfc;
      Peq A := @eq (nfc A);
      Pequiv A := _ |}.

  Definition δε {Δ : Ctx kind} : ε [→] Δ := {| apply_arr (x : dom ε) := match x with end;
                                              arr_hom (x : dom ε) := match x with end |}.

  Lemma δε_unique {Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) :
    δ ∘ δε ≡ δε.
  Proof.
    intros [].
  Qed.

  #[export] Instance Proper_neuapp {κₐ κᵣ Δ} :
    Proper (eq1 ==> eq1 ==> eq) (neu_app : PNeu (κₐ ⇒ κᵣ) Δ → PNf κₐ Δ → _).
  Proof.
    intros ν₁ ν₂ [] μ₁ μ₂ []; reflexivity.
  Qed.


  Definition nfsub (Δ₁ Δ₂ : Ctx kind) :=
    ∀ (a : dom Δ₁) κ (EQ : Δ₁ a = κ), kint κ Δ₂.

  Definition nfsub_map {Γ Δ₁ Δ₂ : Ctx kind} (δ : Δ₁ [→] Δ₂) (η : nfsub Γ Δ₁) : nfsub Γ Δ₂ :=
    λ a κ EQ, fmap δ (η a κ EQ).
  Arguments nfsub_map {Γ _ _} _ _ a κ EQ /.

  Program Definition NSub (Δ : Ctx kind) : PShf (Ctx kind) (Arr := Arr) :=
    {| FO := nfsub Δ;
      Peq Δ' ρ₁ ρ₂ := ∀ a κ EQ, ρ₁ a κ EQ ≅ ρ₂ a κ EQ;
      FA := @nfsub_map Δ
    |}.
  Next Obligation.
    intros Δ'; split.
    - intros ρ a κ EQ; reflexivity.
    - intros ρ₁ ρ₂ EQρ a κ EQ; symmetry; apply EQρ.
    - intros ρ₁ ρ₂ ρ₃ EQρ₁ EQρ₂ a κ EQ; etransitivity; [apply EQρ₁ | apply EQρ₂].
  Qed.
  Next Obligation.
    split.
    - intros Δ₁ Δ₂ δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ a κ EQ; unfold fmap, PShf_funcore; simpl.
      now rewrite (EQρ _ _ EQ), EQδ.
    - intros Δ' ρ a κ EQ; apply fmap_ı.
    - intros Δ₁ Δ₂ Δ₃ δ₂ δ₁ ρ a κ EQ; apply fmap_comp.
  Qed.

  Definition nsub_ext {Δ₁ Δ₂ κ} (ρ : NSub Δ₁ Δ₂) (μ : kint κ Δ₂) : NSub (Δ₁ ▹ κ) Δ₂ :=
    λ x, match x with
         | VZ => λ κ' (EQ : κ = κ'), eq_rect κ (λ κ0 : kind, kint κ0 Δ₂) μ κ' EQ
         | VS x => λ κ EQ, ρ x κ EQ
         end.

  #[export] Instance Proper_ext {Δ₁ Δ₂ κ} : Proper (eq1 ==> eq1 ==> eq1) (@nsub_ext Δ₁ Δ₂ κ).
  Proof.
    intros ρ₁ ρ₂ EQρ μ₁ μ₂ EQμ [| x] κ' EQ; simpl; [| apply EQρ].
    destruct EQ; simpl; assumption.
  Qed.

  Lemma fmap_sub_ext {Δ₁ Δ₂ Δ₃ κ} (δ : Δ₂ [→] Δ₃) (ρ : NSub Δ₁ Δ₂) (μ : kint κ Δ₂) :
    fmap δ (nsub_ext ρ μ) ≅ nsub_ext (fmap δ ρ) (fmap δ μ).
  Proof.
    intros [| x] κ' EQ; simpl in *; [| reflexivity].
    destruct EQ; reflexivity.
  Qed.

End NF.
