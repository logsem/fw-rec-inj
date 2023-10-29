Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic.
Require Import FOmegaEq.Kinds FOmegaEq.Types FOmegaEq.Universe.
Require Import RelationClasses Morphisms FOmegaEq.Presheaves.
Require Import List.

Local Open Scope bind_scope.

Module Interp (PM : Point).
  Module N := NF(PM).
  Export N.

  #[local] Instance Proper_refl_karr1 κₐ κᵣ Δ₁ Δ₂ (ν : PNeu (κₐ ⇒ κᵣ) Δ₁)
    (φ : PArr (PNeu κᵣ) (kint κᵣ) ε)
    (ψ : PArr (kint κₐ) (PNf  κₐ) ε) :
    Proper (equal Δ₁ Δ₂ ==> eq1 ==> eq1)
      (λ δ μ, φ Δ₂ δε ((fmap δ ν) (ψ Δ₂ δε μ))).
  Proof.
    intros δ₁ δ₂ EQδ μ₁ μ₂ EQμ; apply arr_ext; [reflexivity |].
    apply Proper_neuapp; [now rewrite EQδ | now rewrite EQμ].
  Qed.

  #[local] Instance FComp_refl_karr1 κₐ κᵣ Δ (ν : PNeu (κₐ ⇒ κᵣ) Δ)
    (φ : PArr (PNeu κᵣ) (kint κᵣ) ε)
    (ψ : PArr (kint κₐ) (PNf  κₐ) ε) :
    FComp (λ Δ' δ μ, φ Δ' δε (fmap δ ν (ψ Δ' δε μ))).
  Proof.
    intros Δ₁ Δ₂ δ₂ δ₁ μ; rewrite <- arr_fmap; apply arr_ext; [now intros [] |].
    unfold eq1; term_simpl; rewrite map_map_comp'; f_equal.
    now rewrite <- arr_fmap, δε_unique.
  Qed.

  #[local] Instance Proper_refl_ktyp Δ :
    Proper (equal ε Δ ==> eq1 (F := PNeu ⋆) ==> eq1 (A := Δ) (F := kint ⋆))
      (λ (_ : ε [→] Δ) ν, ν).
  Proof.
    intros δ₁ δ₂ EQδ ν₁ ν₂ EQν; assumption.
  Qed.

  #[local] Instance FComp_refl_ktyp :
    FComp (λ (Δ : Ctx kind) (_ : ε [→] Δ) (ν : PNeu ⋆ Δ), ν : kint ⋆ Δ).
  Proof.
    intros Δ₁ Δ₂ δ₂ δ₁ ν; reflexivity.
  Qed.

  #[local] Instance Proper_refl_karr2 κₐ κᵣ Δ
    (φ : PArr (PNeu κᵣ) (kint κᵣ) ε)
    (ψ : PArr (kint κₐ) (PNf  κₐ) ε) :
    Proper (equal ε Δ ==> eq1 ==> eq1)
      (λ (_ : ε [→] Δ) (ν : PNeu (κₐ ⇒ κᵣ) Δ),
        λₖ Δ' δ' μ, φ Δ' δε (fmap δ' ν (ψ Δ' δε μ))).
  Proof.
    intros δ₁ δ₂ EQδ ν₁ ν₂ EQν; now rewrite EQν.
  Qed.

  #[local] Instance FComp_refl_karr2 κₐ κᵣ
    (φ : PArr (PNeu κᵣ) (kint κᵣ) ε)
    (ψ : PArr (kint κₐ) (PNf  κₐ) ε) :
    FComp (λ Δ (_ : ε [→] Δ) (ν : PNeu (κₐ ⇒ κᵣ) Δ),
        (λₖ Δ' δ' μ, φ Δ' δε (fmap δ' ν (ψ Δ' δε μ))) : kint (_ ⇒ _) _).
  Proof.
    intros Δ₁ Δ₂ δ₂ δ₁ ν Δ₃ δ₃ μ; simpl; now rewrite map_map_comp'.
  Qed.

  #[local] Instance Proper_reify_ktyp Δ :
    Proper (equal ε Δ ==> eq1 (F := kint ⋆) ==> eq1 (A := Δ) (F := PNf ⋆))
      (λ (_ : ε [→] Δ) ν, nf_neu ν).
  Proof.
    now intros δ₁ δ₂ EQδ ν₁ ν₂ [].
  Qed.

  #[local] Instance FComp_reify_ktyp :
    FComp (λ (Δ : Ctx kind) (_ : ε [→] Δ) (ν : kint ⋆ Δ), nf_neu ν : PNf ⋆ Δ).
  Proof.
    intros Δ₁ Δ₂ δ₂ δ₁ ν; reflexivity.
  Qed.

  #[local] Instance Proper_reify_karr κₐ κᵣ Δ
    (φ : PArr (PNeu κₐ) (kint κₐ) ε)
    (ψ : PArr (kint κᵣ) (PNf  κᵣ) ε) :
    Proper (equal ε Δ ==> eq1 ==> eq1)
      (λ (_ : ε [→] Δ) (ν : kint (κₐ ⇒ κᵣ) Δ),
        (nf_lam (ψ _ δε (ν _ mk_shift (φ _ δε 0ⁿ%U))))
        : PNf _ _).
  Proof.
    intros δ₁ δ₂ EQδ φ₁ φ₂ EQφ; unfold eq1; term_simpl; f_equal.
    now rewrite EQφ.
  Qed.

  #[local] Instance FComp_reify_karr κₐ κᵣ
    (φ : PArr (PNeu κₐ) (kint κₐ) ε)
    (ψ : PArr (kint κᵣ) (PNf  κᵣ) ε) :
    FComp (λ Δ (_ : ε [→] Δ) (ν : kint (κₐ ⇒ κᵣ) Δ),
        (nf_lam (ψ (Δ ▹ κₐ) δε (ν (Δ ▹ κₐ) mk_shift (φ (Δ ▹ κₐ) δε 0ⁿ%U))))
        : PNf (κₐ ⇒ κᵣ) Δ).
  Proof.
    intros Δ₁ Δ₂ δ₂ δ₁ μ; unfold eq1; term_simpl; f_equal.
    now rewrite <- !arr_fmap, !δε_unique, liftA_mk_shift_comm.
  Qed.

  (** Fig. 13 *)
  Fixpoint reflectI {κ} : PArr (PNeu κ) (kint κ) ε :=
    match κ with
    | ⋆ => λₖ Δ _ ν, ν
    | κₐ ⇒ κᵣ => λₖ Δ _ (ν : PNeu _ _),
        (λₖ Δ' δ' μ, reflectI _ δε (fmap δ' ν (reifyI _ δε μ)))
        : kint (_ ⇒ _) _
    end
  with reifyI {κ} : PArr (kint κ) (PNf κ) ε :=
    match κ with
    | ⋆ => λₖ Δ _ (ν : kint ⋆ _), nf_neu ν : PNf ⋆ _
    | κₐ ⇒ κᵣ => λₖ Δ _ (ν : kint (_ ⇒ _) _),
        ƛ (reifyI _ δε (ν _ mk_shift (@reflectI κₐ _ δε 0ⁿ))) : PNf (_ ⇒ _) Δ
    end%U.

  Definition reify {κ Δ} : kint κ Δ → Nf κ Δ := @reifyI κ Δ δε.
  Definition reflect {κ Δ} : Neu κ Δ → kint κ Δ := @reflectI κ Δ δε.

  Notation "0ⁱ" := (reflect 0ⁿ%U).

  #[export] Instance Proper_reify {κ Δ} : Proper (eq1 ==> eq) (@reify κ Δ).
  Proof.
    intros μ₁ μ₂ EQμ; unfold reify; now rewrite EQμ.
  Qed.

  Lemma reify_map {κ Δ₁ Δ₂} (δ : Δ₁ [→] Δ₂) (μ : kint κ Δ₁) :
    fmap δ (reify μ) = reify (fmap δ μ).
  Proof.
    unfold reify; symmetry; etransitivity; [| apply (arr_fmap _ _ _ reifyI)].
    now rewrite δε_unique.
  Qed.

  Lemma reflect_map {κ Δ₁ Δ₂} (δ : Δ₁ [→] Δ₂) (ν : Neu κ Δ₁) :
    fmap δ (reflect ν) ≅ reflect (fmap δ ν).
  Proof.
    now unfold reflect; rewrite <- arr_fmap, δε_unique.
  Qed.

  #[local] Instance Proper_tlamI κₐ κᵣ Δ Δ₁ Δ₂ (ρ : NSub Δ Δ₁)
    (φ : PArr (NSub (Δ ▹ κₐ)) (kint κᵣ) ε) :
    Proper (equal Δ₁ Δ₂ ==> eq1 ==> eq1)
      (λ δ μ, φ Δ₂ δε (nsub_ext (fmap δ ρ) μ)).
  Proof.
    intros δa δb EQδ μ₁ μ₂ EQμ; now rewrite EQδ, EQμ.
  Qed.

  #[local] Instance FComp_tlamI κₐ κᵣ Δ Δ₁ (ρ : NSub Δ Δ₁)
    (φ : PArr (NSub (Δ ▹ κₐ)) (kint κᵣ) ε) :
    FComp (λ Δ₂ δ μ, φ _ δε (nsub_ext (fmap δ ρ) μ)).
  Proof.
    intros Δ₂ Δ₃ δ₃ δ₂ μ; now rewrite <- arr_fmap, fmap_sub_ext, fmap_comp, δε_unique.
  Qed.

  #[local] Instance Proper_tvar κ (Δ Δ' : Ctx kind) x (EQ : Δ x = κ) :
    Proper (equal ε Δ' ==> eq1 ==> eq1) (λ (_ : ε [→] Δ') (ρ : NSub Δ Δ'), ρ x κ EQ).
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ; apply EQρ.
  Qed.

  #[local] Instance FComp_tvar κ (Δ : Ctx kind) x (EQ : Δ x = κ) :
    FComp (λ Δ' (_ : ε [→] Δ') (ρ : NSub Δ Δ'), ρ x κ EQ).
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ; reflexivity.
  Qed.

  #[local] Instance Proper_tlam κₐ κᵣ Δ Δ'
    (φ : PArr (NSub (Δ ▹ κₐ)) (kint κᵣ) ε) :
    Proper (equal ε Δ' ==> eq1 ==> eq1)
      (λ (_ : ε [→] Δ') (ρ : NSub Δ Δ'),
        λₖ Δ₂ δ₂ μ, φ Δ₂ δε (nsub_ext (fmap δ₂ ρ) μ)).
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ Δ₄ δ μ; term_simpl.
    now rewrite EQρ.
  Qed.

  #[local] Instance FComp_tlam κₐ κᵣ Δ
    (φ : PArr (NSub (Δ ▹ κₐ)) (kint κᵣ) ε) :
    FComp
      (λ (Δ₁ : Ctx kind) (_ : ε [→] Δ₁) (ρ : NSub Δ Δ₁),
        (λₖ Δ₂ δ₂ μ, φ Δ₂ δε (nsub_ext (fmap δ₂ ρ) μ)) : kint (κₐ ⇒ κᵣ) Δ₁).
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ Δ₄ δ₃ μ; term_simpl.
    now rewrite fmap_comp.
  Qed.

  #[local] Instance Proper_tapp κₐ κᵣ Δ Δ'
    (φ : PArr (NSub Δ) (kint (κₐ ⇒ κᵣ)) ε)
    (ψ : PArr (NSub Δ) (kint κₐ) ε) :
    Proper (equal ε Δ' ==> eq1 ==> eq1)
      (λ (δ : ε [→] Δ') (ρ : NSub Δ Δ'), φ Δ' δ ρ Δ' ı (ψ Δ' δ ρ)).
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ; rewrite EQδ, EQρ at 2; now rewrite EQδ, EQρ.
  Qed.

  #[local] Instance FComp_tapp κₐ κᵣ Δ
    (φ : PArr (NSub Δ) (kint (κₐ ⇒ κᵣ)) ε)
    (ψ : PArr (NSub Δ) (kint κₐ) ε) :
    FComp
      (λ (Δ₁ : Ctx kind) (δ : ε [→] Δ₁) (ρ : NSub Δ Δ₁),
        φ Δ₁ δ ρ Δ₁ ı (ψ Δ₁ δ ρ)).
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ; rewrite <- !arr_fmap, arr_fmap; term_simpl.
    now rewrite arrow_comp_id_r, arrow_comp_id_l.
  Qed.

  #[local] Instance Proper_const κ Δ Δ' (μ : kint κ Δ') :
    Proper (equal ε Δ' ==> eq1 ==> eq1) (λ (_ : ε [→] Δ') (_ : NSub Δ Δ'), μ).
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ; reflexivity.
  Qed.

  #[local] Instance FComp_ctor κ Δ (c : tctor κ) :
    FComp (λ Δ' (_ : ε [→] Δ') (_ : NSub Δ Δ'), reflect (neu_ctor c)).
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ EQδ; now rewrite reflect_map.
  Qed.

  #[local] Instance Proper_carr Δ Δ'
    (ψ : PArr (NSub Δ) PNfc ε) (φ : PArr (NSub Δ) (kint ⋆) ε) :
    Proper (equal ε Δ' ==> eq1 ==> eq1)
      (λ (δ : ε [→] Δ') (ρ : NSub Δ Δ'),
        ψ Δ' δ ρ →ᶜ reify (φ Δ' δ ρ) : PNeu ⋆ _)%U.
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ; unfold eq1; term_simpl.
    f_equal; now rewrite EQδ, EQρ.
  Qed.

  #[local] Instance FComp_carr Δ
    (ψ : PArr (NSub Δ) PNfc ε) (φ : PArr (NSub Δ) (kint ⋆) ε) :
    FComp (λ Δ' (δ : ε [→] Δ') (ρ : NSub Δ Δ'),
        ψ Δ' δ ρ →ᶜ reify (φ Δ' δ ρ) : PNeu ⋆ _)%U.
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ; unfold eq1; term_simpl; f_equal.
    - now rewrite arr_fmap.
    - unfold reify; term_simpl; f_equal.
      now rewrite arr_fmap.
  Qed.

  #[local] Instance Proper_cprod Δ Δ'
    (ψ : PArr (NSub Δ) PNfc ε) (φ : PArr (NSub Δ) (kint ⋆) ε) :
    Proper (equal ε Δ' ==> eq1 ==> eq1)
      (λ (δ : ε [→] Δ') (ρ : NSub Δ Δ'),
        ψ Δ' δ ρ ×ᶜ reify (φ Δ' δ ρ) : PNeu ⋆ _)%U.
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ; unfold eq1; term_simpl.
    f_equal; now rewrite EQδ, EQρ.
  Qed.

  #[local] Instance FComp_cprod Δ
    (ψ : PArr (NSub Δ) PNfc ε) (φ : PArr (NSub Δ) (kint ⋆) ε) :
    FComp (λ Δ' (δ : ε [→] Δ') (ρ : NSub Δ Δ'),
        ψ Δ' δ ρ ×ᶜ reify (φ Δ' δ ρ) : PNeu ⋆ _)%U.
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ; unfold eq1; term_simpl; f_equal.
    - now rewrite arr_fmap.
    - unfold reify; term_simpl; f_equal.
      now rewrite arr_fmap.
  Qed.

  #[local] Instance Proper_ceq κ Δ Δ'
    (φ₁ φ₂ : PArr (NSub Δ) (kint κ) ε) :
    Proper (equal ε Δ' ==> eq1 ==> eq1)
      (λ (_ : ε [→] _) (ρ : NSub Δ Δ'),
        reify (φ₁ Δ' δε ρ) ≃ reify (φ₂ Δ' δε ρ) : PNfc _)%U.
  Proof.
    intros δ₁ δ₂ EQδ ρ₁ ρ₂ EQρ; unfold eq1; simpl.
    f_equal; now rewrite EQρ.
  Qed.

  #[local] Instance FComp_ceq κ Δ
    (φ₁ φ₂ : PArr (NSub Δ) (kint κ) ε) :
    FComp
      (λ (Δ' : Ctx kind) (_ : ε [→] Δ') (ρ : NSub Δ Δ'),
        reify (φ₁ Δ' δε ρ) ≃ reify (φ₂ Δ' δε ρ) : PNfc _)%U.
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ; unfold eq1; term_simpl.
    f_equal; now rewrite reify_map, <- arr_fmap, δε_unique.
  Qed.

  (* Fig. 14 *)
  Fixpoint tint {Δ κ} (τ : typ κ Δ) : PArr (NSub Δ) (kint κ) ε :=
    match τ with
    | t_var κ x EQ => λₖ Δ' δ (ρ : NSub Δ Δ'), ρ x _ EQ
    | t_lam τ => λₖ Δ₁ δ₁ ρ,
        (λₖ Δ₂ δ₂ μ, tint τ _ δε (nsub_ext (fmap δ₂ ρ) μ)) : kint (_ ⇒ _) Δ₁
    | t_app σ τ => λₖ Δ₁ δ ρ, tint σ _ δ ρ _ ı (tint τ _ δ ρ)
    | t_ctor c => λₖ _ _ _, reflect c
    | t_carr  ψ τ =>  λₖ Δ₁ δ ρ, constrint ψ _ δ ρ →ᶜ reify (tint τ _ δ ρ) : kint ⋆ _
    | t_cprod ψ τ => λₖ Δ₁ δ ρ, constrint ψ _ δ ρ ×ᶜ reify (tint τ _ δ ρ) : kint ⋆ _
    end%U
  with constrint {Δ} (ψ : constr Δ) : PArr (NSub Δ) PNfc ε :=
    match ψ with
    | c_eq κ τ₁ τ₂ =>
        λₖ Δ₃ δ ρ, reify (tint τ₁ _ δε ρ) ≃ reify (tint τ₂ _ δε ρ) : PNfc _
    end%U.

  #[local] Instance Proper_rel Δ Δ' (p : Point) :
    Proper (equal ε Δ' ==> eq1 ==> eq1)
      (λ (_ : ε [→] _) (_ : NSub Δ Δ'), neu_rel p : kint ⋆ Δ').
  Proof.
    intros δa δb EQδ μ₁ μ₂ EQμ; reflexivity.
  Qed.

  #[local] Instance FComp_rel Δ (p : Point) :
    FComp
      (λ (Δ' : Ctx kind) (_ : ε [→] Δ') (_ : NSub Δ Δ'), neu_rel p : kint ⋆ _).
  Proof.
    intros Δ₂ Δ₃ δ₂ δ₁ ρ; unfold eq1; term_simpl; f_equal.
  Qed.

  (* Interpretation of neutrals/normals, c.f. Sec. 5.3 *)
  Fixpoint neuint {Δ κ} (τ : Neu κ Δ) : PArr (NSub Δ) (kint κ) ε :=
    match τ with
    | neu_var x EQ => λₖ Δ' δ (ρ : NSub Δ Δ'), ρ x _ EQ
    | neu_app σ τ => λₖ Δ₁ δ ρ, neuint σ _ δ ρ _ ı (nfint τ _ δ ρ)
    | neu_ctor c => λₖ _ _ _, reflect c
    | neu_carr  ψ τ =>  λₖ Δ₁ δ ρ, nfconstrint ψ _ δ ρ →ᶜ reify (nfint τ _ δ ρ) : kint ⋆ _
    | neu_cprod ψ τ => λₖ Δ₁ δ ρ, nfconstrint ψ _ δ ρ ×ᶜ reify (nfint τ _ δ ρ) : kint ⋆ _
    | neu_rel p => λₖ Δ₁ δ ρ, neu_rel p : kint ⋆ _
    end%U
  with nfint {Δ κ} (τ : Nf κ Δ) : PArr (NSub Δ) (kint κ) ε :=
    match τ with
    | nf_neu ν => neuint ν
    | nf_lam τ => λₖ Δ₁ δ₁ ρ,
        (λₖ Δ₂ δ₂ μ, nfint τ _ δε (nsub_ext (fmap δ₂ ρ) μ)) : kint (_ ⇒ _) Δ₁
    end%U
  with nfconstrint {Δ} (ψ : nfc Δ) : PArr (NSub Δ) PNfc ε :=
    match ψ with
    | τ₁ ≃ τ₂ => λₖ Δ₃ _ ρ, reify (nfint τ₁ _ δε ρ) ≃ reify (nfint τ₂ _ δε ρ) : PNfc _
    end%U.

  (* Def. 5.3 *)
  Definition η_id {Δ} : NSub Δ Δ := λ x κ EQ, reflect (neu_var x EQ).

  Definition interp {Δ Δ' κ} (τ : typ κ Δ) (η : NSub Δ Δ') : kint κ Δ' :=
    tint τ _ δε η.

  Definition interpC {Δ Δ'} (ψ : constr Δ) (η : NSub Δ Δ') : nfc Δ' :=
    constrint ψ _ δε η.

  Definition interpNeu {Δ Δ' κ} (τ : Neu κ Δ) (η : NSub Δ Δ') : kint κ Δ' :=
    neuint τ _ δε η.

  Definition interpNf {Δ Δ' κ} (τ : Nf κ Δ) (η : NSub Δ Δ') : kint κ Δ' :=
    nfint τ _ δε η.

  Definition interpNfc {Δ Δ'} (ψ : nfc Δ) (η : NSub Δ Δ') : nfc Δ' :=
    nfconstrint ψ _ δε η.

  Notation "〚 τ 〛 η" := (interp τ η) (at level 60).
  Notation "〚 ψ 〛ᶜ η" := (interpC ψ η) (at level 60).

  Lemma interp_fmap {Δ Δ₁ Δ₂ κ} (δ : Δ₁ [→] Δ₂) (τ : typ κ Δ) η :
    fmap δ (〚 τ 〛 η) ≅ 〚 τ 〛 (fmap δ η).
  Proof.
    unfold interp; now rewrite <- arr_fmap, δε_unique.
  Qed.

  Lemma interpC_fmap {Δ Δ₁ Δ₂} (δ : Δ₁ [→] Δ₂) (ψ : constr Δ) η :
    fmap δ (〚 ψ 〛ᶜ η) = 〚 ψ 〛ᶜ (fmap δ η).
  Proof.
    unfold interpC; term_simpl.
    change (eq (A := nfc _)) with (eq1 (F := PNfc) (A := Δ₂)).
    now rewrite <- arr_fmap with (r := constrint ψ), δε_unique.
  Qed.

  Lemma interpNeu_fmap {Δ Δ₁ Δ₂ κ} (δ : Δ₁ [→] Δ₂) (τ : Neu κ Δ) η :
    fmap δ (interpNeu τ η) ≅ interpNeu τ (fmap δ η).
  Proof.
    unfold interpNeu; now rewrite <- arr_fmap, δε_unique.
  Qed.

  Lemma interpNf_fmap {Δ Δ₁ Δ₂ κ} (δ : Δ₁ [→] Δ₂) (τ : Nf κ Δ) η :
    fmap δ (interpNf τ η) ≅ interpNf τ (fmap δ η).
  Proof.
    unfold interpNf; now rewrite <- arr_fmap, δε_unique.
  Qed.

  Lemma interpNfc_fmap {Δ Δ₁ Δ₂} (δ : Δ₁ [→] Δ₂) (ψ : nfc Δ) η :
    fmap δ (interpNfc ψ η) = interpNfc ψ (fmap δ η).
  Proof.
    unfold interpNfc; term_simpl.
    change (eq (A := nfc _)) with (eq1 (F := PNfc) (A := Δ₂)).
    now rewrite <- arr_fmap with (r := nfconstrint ψ), δε_unique.
  Qed.

  Ltac foldArrs :=
    repeat match goal with
      | |- context[ arr _ _ _ (tint ?τ) δε ?η ] =>
          change (arr _ _ _ (tint τ) δε η) with (interp τ η)
      | |- context[ arr _ _ _ (constrint ?ψ) δε ?η ] =>
          change (arr _ _ _ (constrint ψ) δε η) with (interpC ψ η)
      | |- context[ arr _ _ _ (neuint ?τ) δε ?η ] =>
          change (arr _ _ _ (neuint τ) δε η) with (interpNeu τ η)
      | |- context[ arr _ _ _ (nfint ?τ) δε ?η ] =>
          change (arr _ _ _ (nfint τ) δε η) with (interpNf τ η)
      | |- context[ arr _ _ _ (nfconstrint ?ψ) δε ?η ] =>
          change (arr _ _ _ (nfconstrint ψ) δε η) with (interpNfc ψ η)
      | |- context[ arr _ _ _ reflectI δε ?ν ] =>
          change (arr _ _ _ reflectI δε ν) with (reflect ν)
      | |- context[ arr _ _ _ reifyI δε ?μ ] =>
          change (arr _ _ _ reifyI δε μ) with (reify μ)
      | H : context[ arr _ _ _ (tint ?τ) δε ?η ] |- _ =>
          change (arr _ _ _ (tint τ) δε η) with (interp τ η) in H
      | H : context[ arr _ _ _ (constrint ?ψ) δε ?η ] |- _ =>
             change (arr _ _ _ (constrint ψ) δε η) with (interpC ψ η) in H
      | H : context[ arr _ _ _ reflectI δε ?ν ] |- _ =>
             change (arr _ _ _ reflectI δε ν) with (reflect ν) in H
      | H : context[ arr _ _ _ reifyI δε ?μ ] |- _ =>
          change (arr _ _ _ reifyI δε μ) with (reify μ) in H
      end.

  Fixpoint interp_map {Δ₁ Δ₂ Γ κ} (δ : Δ₁ [→] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (τ : typ κ Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ η₂ (δ x) κ (eq_trans (arr_hom δ x) EQ)) →
    〚 fmap δ τ 〛 η₂ ≅ 〚 τ 〛 η₁
  with interpC_map {Δ₁ Δ₂ Γ} (δ : Δ₁ [→] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (ψ : constr Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ η₂ (δ x) κ (eq_trans (arr_hom δ x) EQ)) →
    〚 fmap δ ψ 〛ᶜ η₂ = 〚 ψ 〛ᶜ η₁.
  Proof.
    - intros EQη; destruct τ.
      + symmetry; apply EQη.
      + intros Γ' γ μ; apply interp_map.
        intros [| x] κ EQ; [subst κ; simpl; reflexivity | term_simpl].
        now rewrite EQη.
      + unfold interp; term_simpl; foldArrs.
        now rewrite !interp_map by (exact EQη).
      + reflexivity.
      + unfold interp, eq1; term_simpl; f_equal; foldArrs.
        * now erewrite interpC_map by (exact EQη).
        * now rewrite interp_map by (exact EQη).
      + unfold interp, eq1; term_simpl; f_equal; foldArrs.
        * now erewrite interpC_map by (exact EQη).
        * now rewrite interp_map by (exact EQη).
    - intros EQη; destruct ψ; unfold interpC; term_simpl; f_equal; foldArrs;
        now rewrite interp_map by (exact EQη).
  Qed.

  Lemma interp_shift {Δ Γ κₐ κᵣ} (η : NSub Δ Γ) (μ : kint κₐ Γ) (τ : typ κᵣ Δ) :
    〚 shift τ 〛 (nsub_ext η μ) ≅ 〚 τ 〛 η.
  Proof.
    apply interp_map; intros x κ EQ; subst; reflexivity.
  Qed.

  Lemma interpC_shift {Δ Γ κ} (η : NSub Δ Γ) (μ : kint κ Γ) (ψ : constr Δ) :
    〚 shift ψ 〛ᶜ (nsub_ext η μ) = 〚 ψ 〛ᶜ η.
  Proof.
    apply interpC_map; intros x κ' EQ; subst κ'; reflexivity.
  Qed.

  Fixpoint interp_bind {Δ₁ Δ₂ Γ κ} (ρ : Δ₁ [⇒] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (τ : typ κ Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ 〚 ρ κ x EQ 〛 η₂) →
    〚 bind ρ τ 〛 η₂ ≅ 〚 τ 〛 η₁
  with interpC_bind {Δ₁ Δ₂ Γ} (ρ : Δ₁ [⇒] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (ψ : constr Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ tint (ρ κ x EQ) _ δε η₂) →
    〚 bind ρ ψ 〛ᶜ η₂ = 〚 ψ 〛ᶜ η₁.
  Proof.
    - intros EQη; destruct τ; term_simpl.
      + symmetry; apply EQη.
      + intros Γ' γ μ; apply interp_bind.
        intros [| x] κ EQ; [subst κ; simpl; reflexivity | term_simpl].
        rewrite EQη, interp_shift; apply interp_fmap.
      + unfold interp; term_simpl; foldArrs.
        now rewrite !interp_bind by (exact EQη).
      + reflexivity.
      + unfold eq1, interp; term_simpl; foldArrs; f_equal.
        * now erewrite interpC_bind by (exact EQη).
        * now rewrite interp_bind by (exact EQη).
      + unfold eq1, interp; term_simpl; foldArrs; f_equal.
        * now erewrite interpC_bind by (exact EQη).
        * now rewrite interp_bind by (exact EQη).
    - intros EQη; destruct ψ; unfold interpC; term_simpl; foldArrs.
      f_equal; now rewrite interp_bind by (exact EQη).
  Qed.

  Lemma interp_subst {Δ Γ κₐ κᵣ} (η : NSub Δ Γ) (σ : typ κᵣ (Δ ▹ κₐ)) (τ : typ κₐ Δ) :
    〚 subst σ τ 〛 η ≅ 〚 σ 〛 (nsub_ext η (〚 τ 〛 η)).
  Proof.
    apply interp_bind; intros [| x] κ EQ; [subst |]; simpl; reflexivity.
  Qed.

  Definition ctrue {Δ} (ψ : nfc Δ) : Prop :=
    match ψ with
    | nfc_eq _ ν₁ ν₂ => ν₁ = ν₂
    end.

  Definition injective {Δ Δ' : Ctx kind} (δ : Δ [→] Δ') :=
    ∀ x y : dom Δ, δ x = δ y → x = y.

  Fixpoint inj_map_neu {Δ Δ' κ} (δ : Δ [→] Δ') (HI : injective δ) (ν₁ ν₂ : Neu κ Δ) {struct ν₁} :
    fmap δ ν₁ = fmap δ ν₂ → ν₁ = ν₂
  with inj_map_nf {Δ Δ' κ} (δ : Δ [→] Δ') (HI : injective δ) (μ₁ μ₂ : Nf κ Δ) {struct μ₁} :
    fmap δ μ₁ = fmap δ μ₂ → μ₁ = μ₂
  with inj_map_nfc {Δ Δ'} (δ : Δ [→] Δ') (HI : injective δ) (ψ₁ ψ₂ : nfc Δ) {struct ψ₁} :
    fmap δ ψ₁ = fmap δ ψ₂ → ψ₁ = ψ₂.
  Proof.
    - revert ν₂;
        assert (HH : ∀ κ' (EQ : κ' = κ) (ν₂ : Neu κ' Δ)
                       (EQ' : fmap δ ν₁ = fmap δ (eq_rect κ' (λ κ, Neu κ Δ) ν₂ κ EQ : Neu κ Δ)),
                  ν₁ = eq_rect κ' (λ κ, Neu κ Δ) ν₂ κ EQ); [intros | apply (HH _ eq_refl)].
      destruct ν₁; destruct ν₂; try (destruct EQ); subst; simpl in *; try discriminate; term_simpl in EQ'.
      + inversion EQ'.
        apply HI in H0; subst x0; now apply neuvar_ext.
      + inversion EQ'; subst κₐ0; apply inj_pairT2 in H1, H1, H2.
        apply inj_map_neu in H1; apply inj_map_nf in H2; now subst.
      + inversion EQ'; apply inj_pairT2 in H0; now subst.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'.
        apply inj_map_nf in H1; apply inj_map_nfc in H0; now subst.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; discriminate.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; discriminate.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'.
        apply inj_map_nf in H1; apply inj_map_nfc in H0; now subst.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'.
      + rewrite UIP_refl with (p := EQ) in *; simpl in *; inversion EQ'; reflexivity.
    - revert μ₂;
        assert (HH : ∀ κ' (EQ : κ' = κ) (μ₂ : Nf κ' Δ) (EQ' : fmap δ μ₁ = fmap δ (eq_rect κ' (nf Δ) μ₂ κ EQ : Nf κ Δ)), μ₁ = eq_rect κ' (nf Δ) μ₂ κ EQ);
        [intros | apply (HH _ eq_refl)].
      destruct μ₁; destruct μ₂; inversion EQ; subst;
        rewrite UIP_refl with (p := EQ) in *; simpl in *; term_simpl in EQ'.
      + inversion EQ'; apply inj_map_neu in H0; now subst.
      + inversion EQ'; apply inj_pairT2 in H0, H0; apply inj_map_nf in H0; [now subst | clear -HI].
        intros [| x] [| y] EQ; simpl in *; try discriminate; f_equal; [].
        inversion EQ; now apply HI.
    - intros EQ; destruct ψ₁; destruct ψ₂; term_simpl in EQ; inversion EQ; subst κ0.
      apply inj_pairT2 in H1, H2; apply inj_map_nf in H1, H2; now subst.
  Qed.

  Fixpoint reflect_inj {Δ κ} (ν₁ ν₂ : Neu κ Δ) :
    (reflect ν₁ ≅ reflect ν₂) → ν₁ = ν₂.
  Proof.
    intros EQ; destruct κ; [exact EQ |].
    specialize (EQ (Δ ▹ κ1) mk_shift 0ⁱ).
    simpl in EQ; foldArrs.
    apply reflect_inj in EQ; inversion EQ.
    apply inj_pairT2 in H0, H0.
    revert H0; apply inj_map_neu.
    intros x y EQ'; now inversion EQ'.
  Qed.

  #[export] Instance interp_Proper {Δ Γ κ} : Proper (eq ==> eq1 ==> eq1) (@interp Δ Γ κ).
  Proof.
    intros τ τ' EQτ η₁ η₂ EQη; subst τ'; unfold interp; now rewrite EQη.
  Qed.

  #[export] Instance interpNeu_Proper {Δ Γ κ} : Proper (eq ==> eq1 ==> eq1) (@interpNeu Δ Γ κ).
  Proof.
    intros τ τ' EQτ η₁ η₂ EQη; subst τ'; unfold interpNeu; now rewrite EQη.
  Qed.

  #[export] Instance interpNf_Proper {Δ Γ κ} : Proper (eq ==> eq1 ==> eq1) (@interpNf Δ Γ κ).
  Proof.
    intros τ τ' EQτ η₁ η₂ EQη; subst τ'; unfold interpNf; now rewrite EQη.
  Qed.

  Fixpoint interpNeu_map {Δ₁ Δ₂ Γ κ} (δ : Δ₁ [→] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (τ : Neu κ Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ η₂ (δ x) κ (eq_trans (arr_hom δ x) EQ)) →
    interpNeu (fmap δ τ) η₂ ≅ interpNeu τ η₁
  with interpNf_map {Δ₁ Δ₂ Γ κ} (δ : Δ₁ [→] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (τ : Nf κ Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ η₂ (δ x) κ (eq_trans (arr_hom δ x) EQ)) →
    interpNf (fmap δ τ) η₂ ≅ interpNf τ η₁
  with interpNfc_map {Δ₁ Δ₂ Γ} (δ : Δ₁ [→] Δ₂) (η₁ : NSub Δ₁ Γ) (η₂ : NSub Δ₂ Γ) (ψ : nfc Δ₁) :
    (∀ (x : dom Δ₁) κ (EQ : Δ₁ x = κ), η₁ x κ EQ ≅ η₂ (δ x) κ (eq_trans (arr_hom δ x) EQ)) →
    interpNfc (fmap δ ψ) η₂ = interpNfc ψ η₁.
  Proof.
    - intros EQη; destruct τ.
      + symmetry; apply EQη.
      + unfold interpNeu; term_simpl; foldArrs.
        rewrite (interpNeu_map _ _ _ _ _ η₁).
        * f_equiv.
          apply interpNf_map.
          intros; subst; simpl; apply EQη.
        * intros; subst; simpl; apply EQη.
      + unfold interpNeu; term_simpl; foldArrs.
        reflexivity.
      + unfold interpNeu; term_simpl; foldArrs.
        erewrite interpNfc_map by (exact EQη).
        f_equiv.
        f_equiv.
        apply interpNf_map; assumption.
      + unfold interpNeu; term_simpl; foldArrs.
        erewrite interpNfc_map by (exact EQη).
        f_equiv.
        f_equiv.
        apply interpNf_map; assumption.
      + unfold interpNeu; term_simpl; foldArrs.
        reflexivity.
    - intros EQη; destruct τ.
      + unfold interpNf; term_simpl; foldArrs.
        pose proof (interpNeu_map _ _ Γ ⋆ δ η₁ η₂ ν EQη) as HEQ.
        clear -HEQ.
        simpl in HEQ.
        apply HEQ.
      + intros Γ' γ μ; apply interpNf_map.
        intros [| x] κ EQ; [subst κ; simpl; reflexivity | term_simpl].
        now rewrite EQη.
    - intros EQη; destruct ψ; unfold interpNfc; term_simpl; f_equal; foldArrs;
        now rewrite interpNf_map by (exact EQη).
  Qed.

  Definition precomp_sub {Δ₁ Δ₂ Γ} (η : NSub Δ₂ Γ) (δ : Δ₁ [→] Δ₂) : NSub Δ₁ Γ :=
    λ x κ EQ, η (δ x) κ (eq_trans (arr_hom δ x) EQ).

  (** Fig. 15 *)
  Fixpoint sub_rel {Δ₁ Δ₂ κ} (η : NSub Δ₁ Δ₂) : kint κ Δ₁ → kint κ Δ₂ → Prop :=
    match κ with
    | ⋆ => λ ν₁ ν₂, interpNeu ν₁ η ≅ ν₂
    | κ₁ ⇒ κ₂ =>
        λ φ₁ φ₂, ∀ Δ₁' Δ₂' (δ₁ : Δ₁ [→] Δ₁') (δ₂ : Δ₂ [→] Δ₂') (η' : NSub Δ₁' Δ₂') μ₁ μ₂
                   (EQ : precomp_sub η' δ₁ ≅ fmap δ₂ η)
                   (HA : sub_rel η' μ₁ μ₂),
    sub_rel η' (φ₁ _ δ₁ μ₁) (φ₂ _ δ₂ μ₂)
  end.

  (** Lemma 5.5 *)
  Fixpoint interp_reify {Δ₁ Δ₂ κ} (η : NSub Δ₁ Δ₂) (μ₁ : kint κ Δ₁) μ₂ (HR : sub_rel η μ₁ μ₂) {struct κ} :
    interpNf (reify μ₁) η ≅ μ₂
  with reflect_rel {Δ₁ Δ₂ κ} (η : NSub Δ₁ Δ₂) (ν : Neu κ Δ₁) μ (HR : interpNeu ν η ≅ μ) {struct κ} : sub_rel η (reflect ν) μ.
  Proof.
    - destruct κ; [apply HR |].
      intros Δ₂' δ₂ μ₂'; simpl in HR; unfold reflect; term_simpl; foldArrs.
      apply interp_reify, HR, reflect_rel.
      + intros x κ []; reflexivity.
      + reflexivity.
    - destruct κ; [apply HR |].
      intros Δ₁' Δ₂' δ₁ δ₂ η' μ₁ μ₂ EQη HRA; simpl; apply reflect_rel.
      unfold interpNeu; term_simpl; foldArrs.
      apply interp_reify in HRA.
      rewrite HRA; clear HRA.
      rewrite interpNeu_map with (η₁ := fmap δ₂ η) by (intros; symmetry; apply EQη).
      rewrite <- interpNeu_fmap, HR.
      term_simpl; now rewrite arrow_comp_id_l.
  Qed.

  Definition sub_relS {Γ Δ₁ Δ₂} (η : NSub Δ₁ Δ₂) (η₁ : NSub Γ Δ₁) (η₂ : NSub Γ Δ₂) :=
    ∀ x κ EQ, sub_rel η (η₁ x κ EQ) (η₂ x κ EQ).

  Lemma subrel_fmap {Δ₁ Δ₂ Δ₁' Δ₂' κ} (δ₁ : Δ₁ [→] Δ₁') (δ₂ : Δ₂ [→] Δ₂')
    (η : NSub Δ₁ Δ₂) (η' : NSub Δ₁' Δ₂') (μ₁ μ₂ : kint κ _)
    (EQ : precomp_sub η' δ₁ ≅ fmap δ₂ η)
    (HR : sub_rel η μ₁ μ₂) :
    sub_rel η' (fmap δ₁ μ₁) (fmap δ₂ μ₂).
  Proof.
    destruct κ.
    - simpl; simpl in μ₁.
      rewrite interpNeu_map; [| now intros; symmetry; apply EQ].
      simpl in HR; simpl.
      rewrite <-interpNeu_fmap.
      now apply fmap_proper, HR.
    - intros Δ₁'' Δ₂'' δ₁' δ₂' η'' ν₁ ν₂ EQ' HRν.
      simpl in HR; apply HR, HRν; clear HR.
      intros x κ []; clear κ; specialize (EQ x _ eq_refl);
        specialize (EQ' (δ₁ x) _ (arr_hom δ₁ x)); unfold precomp_sub in *.
      etransitivity; [apply EQ' |].
      term_simpl; rewrite <- fmap_comp; now apply fmap_ext, EQ.
  Qed.

  Lemma sub_relS_ext {Γ Δ₁ Δ₂ κ} (η : NSub Δ₁ Δ₂) (η₁ : NSub Γ Δ₁) (η₂ : NSub Γ Δ₂) (μ₁ : kint κ Δ₁) (μ₂ : kint κ Δ₂)
    (HRμ : sub_rel η μ₁ μ₂)
    (HRη : sub_relS η η₁ η₂) :
    sub_relS η (nsub_ext η₁ μ₁) (nsub_ext η₂ μ₂).
  Proof.
    intros [| x] κ' []; clear κ'; simpl; [apply HRμ | apply HRη].
  Qed.

  Lemma sub_relS_map {Γ Δ₁ Δ₂ Δ₁' Δ₂'} (η : NSub Δ₁ Δ₂) (η' : NSub Δ₁' Δ₂') (δ₁ : Δ₁ [→] Δ₁') (δ₂ : Δ₂ [→] Δ₂') (η₁ : NSub Γ Δ₁) (η₂ : NSub Γ Δ₂)
    (EQ : precomp_sub η' δ₁ ≅ fmap δ₂ η)
    (HR : sub_relS η η₁ η₂) :
    sub_relS η' (fmap δ₁ η₁) (fmap δ₂ η₂).
  Proof.
    intros x κ []; clear κ; term_simpl.
    now eapply subrel_fmap, HR.
  Qed.

  Inductive sub_relC {Δ₁ Δ₂ : Ctx kind} (η : NSub Δ₁ Δ₂) : nfc Δ₁ → nfc Δ₂ → Prop :=
  | srC {κ} {μ₁ μ₂ ν₁ ν₂ : Nf κ _} (HR₁ : reify (interpNf μ₁ η) = ν₁) (HR₂ : reify (interpNf μ₂ η) = ν₂) :
    sub_relC η (nfc_eq _ μ₁ μ₂) (nfc_eq _ ν₁ ν₂).

  (** Lemma 5.6 *)
  Fixpoint interp_rel {Δ₁ Δ₂ Δ₃ κ} (η₁ : NSub Δ₁ Δ₂) (η₂ : NSub Δ₂ Δ₃) (η₃ : NSub Δ₁ Δ₃) (τ : typ κ Δ₁) :
    sub_relS η₂ η₁ η₃ → sub_rel η₂ (interp τ η₁) (interp τ η₃)
  with interp_relC {Δ₁ Δ₂ Δ₃}  (η₁ : NSub Δ₁ Δ₂) (η₂ : NSub Δ₂ Δ₃) (η₃ : NSub Δ₁ Δ₃) (ψ : constr Δ₁) :
    sub_relS η₂ η₁ η₃ → sub_relC η₂ (interpC ψ η₁) (interpC ψ η₃).
  Proof.
    - intros HR; destruct τ.
      + apply HR.
      + intros Δ₂' Δ₃' δ₂ δ₃ η₂' μ₂ μ₃ EQ HRμ; apply interp_rel.
        now eapply sub_relS_ext, sub_relS_map, HR.
      + unfold reflect; term_simpl; foldArrs.
        assert (HT := interp_rel _ _ _ _ η₁ η₂ η₃ τ1 HR); simpl in HT; apply HT, interp_rel, HR.
        intros x κ []; clear κ; unfold precomp_sub; term_simpl.
        now rewrite fmap_ı.
      + unfold reflect; term_simpl.
        apply reflect_rel; reflexivity.
      + simpl; unfold eq1, interpNeu, interp; term_simpl; foldArrs.
        f_equal; [| f_equal; now apply interp_rel with (κ := ⋆)].
        apply interp_relC with (ψ := ψ) in HR; inversion HR; unfold interpC; term_simpl; foldArrs.
        unfold interpNfc; term_simpl; foldArrs.
        now f_equiv.
      + simpl; unfold eq1, interp, interpNeu; term_simpl; foldArrs.
        f_equal; [| f_equal; now apply interp_rel with (κ := ⋆)].
        apply interp_relC with (ψ := ψ) in HR; inversion HR; unfold interpC, interpNfc; term_simpl; foldArrs.
        now f_equal.
    - intros HR; destruct ψ; unfold interpC; term_simpl; split; foldArrs;
        now apply Proper_reify, interp_reify, interp_rel.
  Qed.

  Fixpoint reinterp_neu {Δ κ} (ν : Neu κ Δ) : interpNeu ν η_id ≅ reflect ν
  with reinterp_nf {Δ κ} (μ : Nf κ Δ) : reify (interpNf μ η_id) = μ
  with reinterp_nfc {Δ} (ψ : nfc Δ) : interpNfc ψ η_id = ψ.
  Proof.
    - destruct ν.
      + reflexivity.
      + unfold interpNeu; term_simpl; foldArrs.
        rewrite reinterp_neu; simpl; foldArrs.
        rewrite map_id'; foldArrs.
        rewrite reinterp_nf.
        reflexivity.
      + reflexivity.
      + unfold eq1, interpNeu; term_simpl; foldArrs.
        unfold reflect; simpl; foldArrs.
        congruence.
      + unfold eq1, interpNeu; term_simpl; foldArrs.
        unfold reflect; simpl; foldArrs.
        congruence.
      + unfold interpNeu; term_simpl; foldArrs.
        reflexivity.
    - destruct μ.
      + simpl.
        unfold interpNf; simpl; foldArrs.
        now rewrite (reinterp_neu Δ ⋆ ν).
      + unfold reflect, reify; term_simpl; foldArrs; f_equal.
        rewrite <- reinterp_nf; apply Proper_reify, interpNf_Proper; [reflexivity |].
        intros [| x] κ []; simpl; [reflexivity |]; unfold η_id; term_simpl.
        unfold shift; rewrite reflect_map; reflexivity.
    - destruct ψ; unfold interpNfc; term_simpl; foldArrs.
      congruence.
  Qed.

  Fixpoint interpNeu_rel {Δ₁ Δ₂ Δ₃ κ} (η₁ : NSub Δ₁ Δ₂) (η₂ : NSub Δ₂ Δ₃) (η₃ : NSub Δ₁ Δ₃) (τ : Neu κ Δ₁) :
    sub_relS η₂ η₁ η₃ → sub_rel η₂ (interpNeu τ η₁) (interpNeu τ η₃)
  with interpNf_rel {Δ₁ Δ₂ Δ₃ κ} (η₁ : NSub Δ₁ Δ₂) (η₂ : NSub Δ₂ Δ₃) (η₃ : NSub Δ₁ Δ₃) (τ : Nf κ Δ₁) :
    sub_relS η₂ η₁ η₃ → sub_rel η₂ (interpNf τ η₁) (interpNf τ η₃)
  with interpNfc_relC {Δ₁ Δ₂ Δ₃}  (η₁ : NSub Δ₁ Δ₂) (η₂ : NSub Δ₂ Δ₃) (η₃ : NSub Δ₁ Δ₃) (ψ : nfc Δ₁) :
    sub_relS η₂ η₁ η₃ → sub_relC η₂ (interpNfc ψ η₁) (interpNfc ψ η₃).
  Proof.
    - intros HR; destruct τ.
      + apply HR.
      + unfold interpNeu; term_simpl; foldArrs.
        assert (HT := interpNeu_rel _ _ _ _ η₁ η₂ η₃ τ HR); simpl in HT; apply HT.
        intros x κ []; clear κ; unfold precomp_sub; term_simpl.
        now rewrite fmap_ı.
        now apply interpNf_rel.
      + unfold interpNeu; term_simpl.
        apply reflect_rel; reflexivity.
      + unfold interpNeu; term_simpl.
        unfold interpNeu; term_simpl; foldArrs.
        f_equiv.
        * destruct (interpNfc_relC Δ₁ Δ₂ Δ₃ η₁ η₂ η₃ φ HR).
          unfold interpNfc; simpl.
          subst.
          reflexivity.
        * rewrite (interpNf_rel Δ₁ Δ₂ Δ₃ ⋆ η₁ η₂ η₃ μ HR).
          reflexivity.
      + unfold interpNeu; term_simpl.
        unfold interpNeu; term_simpl; foldArrs.
        f_equiv.
        * destruct (interpNfc_relC Δ₁ Δ₂ Δ₃ η₁ η₂ η₃ φ HR).
          unfold interpNfc; simpl.
          subst.
          reflexivity.
        * rewrite (interpNf_rel Δ₁ Δ₂ Δ₃ ⋆ η₁ η₂ η₃ μ HR).
          reflexivity.
      + simpl; unfold eq1, interpNeu, reflect; term_simpl; foldArrs.
        reflexivity.
    - intros HR; destruct τ.
      + unfold interpNf; term_simpl; foldArrs.
        apply (interpNeu_rel Δ₁ Δ₂ Δ₃ ⋆ η₁ η₂ η₃ ν HR).
      + simpl; unfold eq1, interpNf; term_simpl; foldArrs.
        intros Δ₂' Δ₃' δ₂ δ₃ η₂' μ₂ μ₃ EQ HRμ; apply interpNf_rel.
        now eapply sub_relS_ext, sub_relS_map, HR.
    - intros HR; destruct ψ; unfold interpNfc; term_simpl; split; foldArrs;
        now apply Proper_reify, interp_reify, interpNf_rel.
  Qed.

  (** Lemma 5.4 *)
  Lemma reify_refl_inj {Γ Δ κ} (η : NSub Γ Δ) (τ₁ τ₂ : typ κ Γ)
    (HRη : sub_relS η_id η η)
    (EQ : reify (interp τ₁ η) = reify (interp τ₂ η)) :
    interp τ₁ η ≅ interp τ₂ η.
  Proof.
    erewrite <- interp_reify by (apply interp_rel, HRη).
    rewrite EQ; apply interp_reify, interp_rel, HRη.
  Qed.

  Lemma reify_refl_inj' {Γ Δ κ} (η : NSub Γ Δ) (τ₁ τ₂ : Neu κ Γ)
    (HRη : sub_relS η_id η η)
    (EQ : reify (interpNeu τ₁ η) = reify (interpNeu τ₂ η)) :
    interpNeu τ₁ η ≅ interpNeu τ₂ η.
  Proof.
    erewrite <- interp_reify by apply interpNeu_rel, HRη.
    rewrite EQ.
    apply interp_reify, interpNeu_rel, HRη.
  Qed.

  Instance Proper_subrel {Δ₁ Δ₂ κ} η : Proper (Peq (kint κ) Δ₁ ==> Peq (kint κ) Δ₂ ==> iff) (sub_rel η).
  Proof.
    revert Δ₁ Δ₂ η; induction κ; intros.
    - intros μ₁ μ₂ EQμ ν₁ ν₂ EQν; simpl in *; subst; reflexivity.
    - intros μ₁ μ₂ EQμ ν₁ ν₂ EQν; split; intros HH.
      + intros Γ₁ Γ₂ δ₁ δ₂ η' ψ₁ ψ₂ EQ Rψ; simpl in HH.
        rewrite <- EQμ, <- EQν; now apply HH.
      + intros Γ₁ Γ₂ δ₁ δ₂ η' ψ₁ ψ₂ EQ Rψ; simpl in HH.
        rewrite EQμ, EQν; now apply HH.
  Qed.

  Lemma reinterpret_ext {Δ κ} (τ : typ ⋆ (Δ ▹ κ)) (η : NSub Δ ε) μ (HRη : sub_relS η_id η η) :
    interpNf (reify (〚τ 〛 (nsub_ext (shift η) 0ⁱ))) (nsub_ext (fmap ı%bind η_id) μ) =
      〚τ〛 (nsub_ext η μ).
  Proof.
    eapply (interp_reify (κ := Kinds.KTyp)).
    apply interp_rel; intros [| x] κ' EQ; subst; simpl.
    - apply reflect_rel; unfold reflect; simpl; reflexivity.
    - term_simpl.
      rewrite <- (fmap_ı (η x _ eq_refl)) at 2.
      apply subrel_fmap with η_id, HRη.
      intros [].
  Qed.

  Lemma reify_reflect_inj {Δ κ} {ν₁ ν₂ : Neu κ Δ} (EQ : reify (reflect ν₁) = reify (reflect ν₂)) :
    ν₁ = ν₂.
  Proof.
    rewrite <- !reinterp_neu in EQ.
    apply reflect_inj.
    rewrite <-2reinterp_neu.
    apply reify_refl_inj'; [| assumption].
    intros x κ' []; now apply reflect_rel.
  Qed.

  Lemma ctrue_map {Δ₁ Δ₂} (δ : Δ₁ [→] Δ₂) (ψ : nfc Δ₁) :
    ctrue ψ → ctrue (fmap δ ψ).
  Proof.
    intros HT; destruct ψ; simpl in *; now rewrite HT.
  Qed.

  Definition sempf Δ (Ψ : list (constr Δ)) (φ : constr Δ) :=
    ∀ Γ (η : NSub Δ Γ),
    sub_relS η_id η η →
    (∀ ψ, In ψ Ψ → ctrue (〚 ψ 〛ᶜ η)) → ctrue (〚 φ 〛ᶜ η).

  Inductive tctd' (Δ : Ctx kind) (κ : kind) : Neu κ Δ → ∀ κ' : kind, tctor κ' → Prop :=
    inj_ctor' : ∀ c : tctor κ, tctd' Δ κ (neu_ctor c) κ c
  | inj_app' : ∀ (κₐ κ' : kind) (σ : Neu (κₐ ⇒ κ) Δ) (τ : nf Δ κₐ) (c : tctor κ'), tctd' Δ (κₐ ⇒ κ) σ κ' c → tctd' Δ κ (neu_app σ τ) _ c.

  Arguments tctd' {Δ κ} _ {κ'} _.
  Arguments inj_ctor' {Δ κ} c.
  Arguments inj_app' {Δ κ κₐ κ'} σ τ c HI.

  Lemma tctd_neu {Δ Γ κ κ'} (η : NSub Δ Γ) (σ : typ κ Δ) (c : tctor κ') (HC : tctd σ c) :
    ∃ (ν : Neu κ Γ), interp σ η ≅ reflect ν ∧ tctd' ν c.
  Proof.
    induction HC.
    - exists (neu_ctor c); split; [reflexivity | constructor].
    - destruct IHHC as [ν [EQ HC']].
      exists (neu_app ν (reify (interp τ η))); unfold interp; term_simpl; foldArrs.
      split; [| econstructor; eassumption].
      rewrite EQ; simpl; foldArrs; now rewrite map_id'.
  Qed.

  (** Lemma 5.7, part 1 (provability) *)
  Lemma tproves_int Δ (Ψ : list (constr Δ)) (φ : constr Δ) (HP : Ψ ⊩ φ) : sempf Δ Ψ φ.
  Proof.
    induction HP; simpl; intros Γ η HRη HC'.
    - apply HC', HIn.
    - simpl; subst κ; rewrite UIP_refl with (p := EQ₂); reflexivity.
    - simpl; unfold reify; simpl; foldArrs; f_equal.
      apply IHHP.
      + eapply sub_relS_ext, sub_relS_map, HRη; [now apply reflect_rel |].
        intros x κ []; unfold precomp_sub, η_id; term_simpl.
        unfold shift; now rewrite reflect_map.
      + intros ψ' HIn; rewrite in_map_iff in HIn; destruct HIn as [ψ [EQ HIn]]; subst ψ'.
        rewrite interpC_shift, <- @interpC_fmap.
        apply ctrue_map, HC', HIn.
    - unfold interpC; term_simpl; foldArrs.
      specialize (IHHP1 _ η HRη HC'); specialize (IHHP2 _ η HRη HC'); simpl in *; foldArrs.
      apply reify_refl_inj in IHHP1, IHHP2; [| assumption ..].
      apply Proper_reify; now rewrite IHHP1, IHHP2.
    - simpl; reflexivity.
    - simpl; unfold eq1, reify; term_simpl; foldArrs; f_equal; f_equal.
      now apply IHHP.
    - simpl; unfold eq1, reify; term_simpl; foldArrs; f_equal; f_equal.
      now apply IHHP.
    - simpl; symmetry; now apply IHHP.
    - simpl; etransitivity; [now apply IHHP1 | now apply IHHP2].
    - simpl; unfold reify; term_simpl; foldArrs.
      f_equal; apply Proper_reify.
      rewrite interp_shift; unfold shift; rewrite <- interp_fmap; term_simpl.
      now rewrite arrow_comp_id_l.
    - simpl; unfold reify; term_simpl; foldArrs.
      now apply Proper_reify; rewrite fmap_ı, interp_subst.
    - term_simpl; foldArrs; specialize (IHHP _ η HRη HC').
      apply reify_refl_inj in IHHP; [| assumption].
      unfold interp in IHHP; simpl in IHHP; foldArrs.
      apply (@tctd_neu Δ _ _ _ η) in HI₁, HI₂.
      destruct HI₁ as [ν₁ [EQ₁ _]], HI₂ as [ν₂ [EQ₂ _]].
      rewrite EQ₁, EQ₂ in IHHP; simpl in IHHP; foldArrs.
      apply reflect_inj in IHHP; inversion IHHP; now apply inj_pairT2 in H1.
    - term_simpl; foldArrs; specialize (IHHP _ η HRη HC').
      apply reify_refl_inj in IHHP; [| assumption].
      unfold interp in IHHP; simpl in IHHP; foldArrs.
      apply (@tctd_neu Δ _ _ _ η) in HI₁, HI₂.
      destruct HI₁ as [ν₁ [EQ₁ _]], HI₂ as [ν₂ [EQ₂ _]].
      rewrite EQ₁, EQ₂ in IHHP; simpl in IHHP; foldArrs.
      rewrite !map_id' in IHHP; apply reflect_inj in IHHP.
      inversion IHHP; apply inj_pairT2, inj_pairT2 in H0; subst.
      apply Proper_reify; now rewrite EQ₁, EQ₂.
    - specialize (IHHP _ η HRη HC'); simpl in *; unfold reify in IHHP; term_simpl in IHHP; foldArrs.
      inversion IHHP; congruence.
    - specialize (IHHP _ η HRη HC'); simpl in *; unfold reify in IHHP; term_simpl in IHHP; foldArrs.
      inversion IHHP; congruence.
    - specialize (IHHP1 _ η HRη HC'); simpl in *; unfold reify in IHHP1; term_simpl in IHHP1; foldArrs.
      specialize (IHHP2 _ η HRη HC'); simpl in *; unfold reify in IHHP2; term_simpl in IHHP2; foldArrs.
      inversion IHHP1.
      congruence.
    - specialize (IHHP1 _ η HRη HC'); simpl in *; unfold reify in IHHP1; term_simpl in IHHP1; foldArrs.
      specialize (IHHP2 _ η HRη HC'); simpl in *; unfold reify in IHHP2; term_simpl in IHHP2; foldArrs.
      inversion IHHP1.
      congruence.
  Qed.

  Lemma tctd_neu_cast {Δ : Ctx kind} {κ κ' : kind} {c : tctor κ} {c' : tctor κ'} (HC : @tctd' Δ κ (neu_ctor c) κ' c')
    : existT _ κ c = existT _ κ' c'.
  Proof.
    destruct c; inversion HC; subst;
      repeat (match goal with
              | H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pairT2 in H
              end); now subst.
  Qed.

  Lemma tctd_neu_discr {Γ κ κ₁ κ₂} {ν : Neu κ Γ} {c₁ : tctor κ₁} {c₂ : tctor κ₂} (HC₁ : tctd' ν c₁) (HC₂ : tctd' ν c₂) (HD : cdiscrK c₁ c₂) : False.
  Proof.
    induction HC₁.
    - unfold cdiscrK in HD.
      destruct (kindEqDec.eq_dec κ κ₂); [subst; simpl in * |].
      + apply tctd_neu_cast in HC₂.
        apply inj_pairT2 in HC₂; subst.
        revert HD; apply irreflexivity.
      + inversion HC₂; subst; contradiction.
    - inversion HC₂; subst.
      apply inj_pairT2 in H1, H1, H2, H4; subst; now eauto.
  Qed.

  (** Lemma 5.7, part 2 (discriminability) *)
  Lemma tdiscr_int {Δ Γ} (ψ : constr Δ) (η : NSub Δ Γ) (HD : ⊮ ψ) : ¬ ctrue (〚ψ〛ᶜ η).
  Proof.
    destruct HD.
    - apply (@tctd_neu _ _ _ _ η) in HI₁; destruct HI₁ as [ν₁ [EQ₁ HC₁]]; simpl; foldArrs.
      apply (@tctd_neu _ _ _ _ η) in HI₂; destruct HI₂ as [ν₂ [EQ₂ HC₂]]; simpl; foldArrs.
      intros EQ.
      assert (HH : ν₁ = ν₂) by (apply reify_reflect_inj; now rewrite <- EQ₁, <- EQ₂); subst.
      eapply tctd_neu_discr; [apply HC₁ | apply HC₂ | apply HD].
    - apply (@tctd_neu _ _ _ _ η) in HI; destruct HI as [ν [EQ HC]]; simpl; foldArrs.
      rewrite EQ; unfold reify, reflect; simpl; intros EQ'.
      inversion EQ'; subst; clear EQ'; now inversion HC.
    - apply (@tctd_neu _ _ _ _ η) in HI; destruct HI as [ν [EQ HC]]; simpl; foldArrs.
      rewrite EQ; unfold reify, reflect; simpl; intros EQ'.
      inversion EQ'; subst; clear EQ'; now inversion HC.
    - apply (@tctd_neu _ _ _ _ η) in HI; destruct HI as [ν [EQ HC]]; simpl; foldArrs.
      rewrite EQ; unfold reify, reflect; simpl; intros EQ'.
      inversion EQ'; subst; clear EQ'; now inversion HC.
    - apply (@tctd_neu _ _ _ _ η) in HI; destruct HI as [ν [EQ HC]]; simpl; foldArrs.
      rewrite EQ; unfold reify, reflect; simpl; intros EQ'.
      inversion EQ'; subst; clear EQ'; now inversion HC.
    - simpl; discriminate.
    - simpl; discriminate.
  Qed.

  (** Lemma 4.1 *)
  Lemma consistency {ψ : constr ε} (HP : nil ⊩ ψ) (HD : ⊮ ψ) : False.
  Proof.
    eapply tdiscr_int with (η := η_id); [eassumption |].
    eapply tproves_int; [eassumption | now intros [] | now intros ψ' []].
  Qed.

End Interp.
