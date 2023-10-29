Require Import Utf8.
Require Import Binding.Lib Binding.Intrinsic Binding.Auto.
Require Import FOmegaEq.Kinds FOmegaEq.Universe FOmegaEq.Interp.
Require Import FOmegaEq.Presheaves.
Require Import List.

Module GView (PM : Point).
  Module Export I := Interp(PM).

  Definition pk := sigT (λ κ, Nf κ ε).

  Fixpoint fkind {P : kind → Type} κ (η : list (sigT P)) : kind :=
    match η with
    | nil => κ
    | cons pk η => projT1 pk ⇒ fkind κ η
    end.

  (* closed normals at ground kind *)
  Inductive gtyp :=
  | GAbstract : Point -> gtyp
  | GUnit | GVoid
  | GProd : gtyp → gtyp → gtyp
  | GSum  : gtyp → gtyp → gtyp
  | GArr  : gtyp → gtyp → gtyp
  | GAll  κ : nf ε (κ ⇒ ⋆) → gtyp
  | GXist κ : nf ε (κ ⇒ ⋆) → gtyp
  | GRec  κ (μ : Nf (κ ⇒ κ) ε) (η : list pk) (EQ : fkind ⋆ η = κ) : gtyp
  | GCArr : nfc ε → gtyp → gtyp
  | GCPrd : nfc ε → gtyp → gtyp.

  Declare Scope gview_scope.
  Delimit Scope gview_scope with G.

  Notation "σ →ᵗ τ" := (GArr σ τ) (at level 55, right associativity) : gview_scope.
  Notation "τ₁ + τ₂" := (GSum τ₁ τ₂) (at level 50, left associativity) : gview_scope.
  Notation "τ₁ × τ₂" := (GProd τ₁ τ₂) (at level 40, left associativity) : gview_scope.
  Notation "χ →ᶜ τ" := (GCArr χ τ) (at level 55, right associativity) : gview_scope.
  Notation "χ ×ᶜ τ" := (GCPrd χ τ) (at level 40, left associativity) : gview_scope.
  Notation "∀ᵗ κ , τ" := (GAll κ τ) (at level 60) : gview_scope.
  Notation "∃ᵗ κ , τ" := (GXist κ τ) (at level 60) : gview_scope.
  Notation "⊥" := GVoid : gview_scope.
  Notation "⊤" := GUnit : gview_scope.

  Class Applicable (F : kind → Type) (A : kind → Type) :=
    app : ∀ {κₐ κᵣ}, F (κₐ ⇒ κᵣ) → A κₐ → F κᵣ.

  #[export] Instance AppNeu {Δ} : Applicable (λ κ, Neu κ Δ) (λ κ, Nf κ Δ) :=
    λ κₐ κᵣ ν μ, ν μ.
  #[export] Instance AppKint {Δ} : Applicable (λ κ, kint κ Δ) (λ κ, kint κ Δ) :=
    λ κₐ κᵣ φ μ, φ _ ı%bind μ.

  Fixpoint applyAll {F A : kind → Type} {κ} {FA : Applicable F A} η : F (fkind κ η) → F κ :=
    match η return F (@fkind (λ κ, A κ) κ η) → F κ with
    | nil => λ ν, ν
    | cons (existT _ κ μ) η => λ ν, applyAll η (app ν μ)
    end.

  Fixpoint unView (g : gtyp) : Neu ⋆ ε :=
    match g with
    | GAbstract P => neu_rel P
    | GUnit => ⊤
    | GVoid => ⊥
    | GProd g₁ g₂ => unView g₁ × unView g₂
    | GSum  g₁ g₂ => unView g₁ + unView g₂
    | GArr  g₁ g₂ => unView g₁ →ᵗ unView g₂
    | GAll  κ μ => tc_all  κ μ
    | GXist κ μ => tc_xist κ μ
    | GRec κ μ η EQ =>
        match EQ in eq _ κ return Neu κ ε → Neu ⋆ ε with
          eq_refl => applyAll (F := λ κ, Neu κ ε) η
        end (tc_rec κ μ)
    | GCArr χ g => χ →ᶜ unView g
    | GCPrd χ g => χ ×ᶜ unView g
    end%U.

  Definition arg (κ : kind) : Type :=
    match κ with
    | ⋆ => gtyp
    | _ => Nf κ ε
    end.

  Definition mapT {P Q : kind → Type} (f : ∀ κ, P κ → Q κ) (p : sigT P) : sigT Q :=
    match p with existT _ κ p => existT _ κ (f κ p) end.

  Lemma fkind_map {P Q : Kinds.kind → Type} (f : ∀ κ, P κ → Q κ) κ κ' (η : list (sigT P))
    (EQ : fkind κ' η = κ) : fkind κ' (List.map (mapT f) η) = κ.
  Proof.
    subst; induction η as [| [κ'' ν]]; intros; simpl in *; congruence.
  Qed.

  Definition unArg κ : arg κ → Nf κ ε :=
    match κ return arg κ → nf ε κ with
    | ⋆ => λ g, nf_neu (unView g)
    | _ => λ a, a
    end.

  Fixpoint gFun (κ : kind) : Type :=
    match κ with
    | ⋆ => gtyp
    | κₐ ⇒ κᵣ => arg κₐ → gFun κᵣ
    end.

  #[export] Instance AppGFun : Applicable gFun arg :=
    λ κₐ κᵣ f a, f a.

  Lemma kind_typ_arr {κ₁ κ₂} : ¬ ⋆ = κ₁ ⇒ κ₂.
  Proof.
    discriminate.
  Qed.

  Lemma kind_arr_inv {κ₁ κ₂ κ₁' κ₂'} (EQ : κ₁ ⇒ κ₂ = κ₁' ⇒ κ₂') : κ₁ = κ₁' ∧ κ₂ = κ₂'.
  Proof.
    now inversion EQ.
  Qed.

  Program Definition viewC (η : list (sigT arg)) (c : tctor (fkind ⋆ η)) : gtyp :=
    match c in tctor κ return fkind ⋆ η = κ → gtyp with
    | tc_unit => λ _, ⊤
    | tc_void => λ _, ⊥
    | tc_arr  => λ EQ, applyAll η (eq_rect_r gFun (GArr : gFun (⋆ ⇒ ⋆ ⇒ ⋆)) EQ)
    | tc_sum  => λ EQ, applyAll η (eq_rect_r gFun (GSum : gFun (⋆ ⇒ ⋆ ⇒ ⋆)) EQ)
    | tc_prod  => λ EQ, applyAll η (eq_rect_r gFun (GProd : gFun (⋆ ⇒ ⋆ ⇒ ⋆)) EQ)
    | tc_all κ  => λ EQ, applyAll η (eq_rect_r gFun (GAll κ : gFun ((κ ⇒ ⋆) ⇒ ⋆)) EQ)
    | tc_xist κ => λ EQ, applyAll η (eq_rect_r gFun (GXist κ : gFun ((κ ⇒ ⋆) ⇒ ⋆)) EQ)
    | tc_rec κ  => match η with
                  | nil => _
                  | cons (existT _ κ' μ) η => λ EQ : κ' ⇒ fkind ⋆ η = (κ ⇒ κ) ⇒ κ,
                        let (EQ₁, EQ₂) := kind_arr_inv EQ
                        in match EQ₂ in _ = κ return κ' = κ ⇒ κ → gtyp with
                           | eq_refl => λ EQ,
                               GRec _ (eq_rect _ arg μ _ EQ) (map (mapT unArg) η)
                                 (fkind_map unArg _ _ η eq_refl)
                           end EQ₁
                  end
    end%G eq_refl.

  Fixpoint view {κ} (ν : neu ε κ) : ∀ (η : list (sigT arg)) (EQ : fkind ⋆ η = κ), gtyp :=
  λ η, match ν in neu _ κ return fkind ⋆ η = κ → gtyp with
       | neu_rel p => λ _, GAbstract p
       | neu_var x _ => λ _, match x with end
       | neu_app ν μ => λ EQ, view ν (existT _ _ (mkArg μ) :: η) (f_equal _ EQ)
       | neu_ctor c => λ EQ, match EQ in _ = κ return tctor κ → gtyp with
                              eq_refl => viewC η
                            end c
       | neu_carr χ ν => λ _, χ →ᶜ mkArg ν
       | neu_cprod χ ν => λ _, χ ×ᶜ mkArg ν
       end%G
  with mkArg {κ} (μ : nf ε κ) : arg κ :=
         match μ in nf _ κ return arg κ with
         | nf_neu ν => view ν nil eq_refl
         | nf_lam μ => nf_lam μ
         end.

  Lemma fkind_app {P : Kinds.kind → Type} κ (η₁ η₂ : list (sigT P)) :
    fkind κ (η₁ ++ η₂) = fkind (fkind κ η₂) η₁.
  Proof.
    induction η₁; simpl; congruence.
  Defined.

  Require Import FOmegaEq.Types.

  #[export] Instance AppTyp {Δ} : Applicable (λ κ, typ κ Δ) (λ κ, typ κ Δ) :=
    λ κₐ κᵣ σ τ, σ τ.

  Arguments app {F A _ κₐ κᵣ} _ _ /.
  Arguments AppTyp /.
  Arguments AppKint /.
  Arguments AppNeu /.

  Definition viewG (ν : neu ε ⋆) : gtyp := view ν nil eq_refl.

  Definition pkt' (p : pk) : sigT (λ x, kint x ε) :=
    match p with
      existT _ κ ν => existT _ κ (interpNf ν η_id)
    end.

  Lemma fkm_pkt' κ η (EQ : fkind ⋆ η = κ) : fkind ⋆ (List.map pkt' η) = κ.
  Proof.
    apply fkind_map, EQ; intros [κ' μ]; reflexivity.
  Qed.

  Lemma applyAll_app {F A : kind → Type} {FA : Applicable F A} κ η₁ η₂ v :
    applyAll η₂ (applyAll η₁ v) =
      match fkind_app _ η₁ η₂ in _ = κ' return F κ' → F κ with
      | eq_refl => applyAll (η₁ ++ η₂)
      end v.
  Proof.
    induction η₁ as [| [κₐ μ]]; simpl in *.
    - reflexivity.
    - rewrite IHη₁; clear IHη₁.
      generalize (fkind_app κ η₁ η₂) as EQ.
      generalize (η₁ ++ η₂) as η; intros η; revert v.
      fold (fkind (fkind κ η₂) η₁).
      generalize (fkind (fkind κ η₂) η₁); intros; subst.
      now rewrite UIP_refl with (p := eq_trans eq_refl (f_equal (KArr κₐ) eq_refl)).
  Qed.

  Lemma baz {Δ κ κ'} τ₁ τ₂ σ₁ σ₂ (HR : rel_app κ τ₁ τ₂ κ' σ₁ σ₂) :
    ∃ ζ EQ,
      σ₁ = match EQ in _ = κ return typ κ Δ → typ κ' Δ with
           | eq_refl => applyAll (F := λ κ, typ κ Δ) ζ
           end τ₁ ∧
        σ₂ = match EQ in _ = κ return typ κ Δ → typ κ' Δ with
             | eq_refl => applyAll (F := λ κ, typ κ Δ) ζ
             end τ₂.
  Proof.
    induction HR.
    - exists nil, eq_refl; now simpl.
    - destruct IHHR as [ζ [EQ [EQ₁ EQ₂]]]; subst κ; simpl in *.
      exists (ζ ++ (cons (existT _ κₐ τ) nil)), (fkind_app _ _ _); split;
        rewrite <- (applyAll_app (F := λ κ, typ κ Δ)); simpl; congruence.
  Qed.

  Definition intP {Δ Δ'} (η : NSub Δ Δ') (p : sigT (type Δ)) : sigT (λ κ, kint κ Δ') :=
    match p with existT _ κ τ => existT _ κ (interp τ η) end.

  Lemma fkm_intP {Δ Δ' κ κᵣ} ζ (η : NSub Δ Δ') (EQ : fkind κ ζ = κᵣ) :
    fkind κ (map (intP η) ζ) = κᵣ.
  Proof.
    apply fkind_map, EQ; intros [κ' μ]; reflexivity.
  Qed.

  Lemma reflAppAll {Δ Δ' κ κᵣ} (ζ : list (sigT (λ κ, typ κ Δ))) (τ : typ κᵣ Δ) (η : NSub Δ Δ') (EQ : fkind κ ζ = κᵣ) :
    interp
      (match EQ in _ = κ' return typ κ' Δ → typ κ Δ with
       | eq_refl => applyAll (F := λ κ, typ κ Δ) ζ
       end τ) η ≅
      match fkm_intP ζ η EQ in _ = κ' return kint κ' Δ' → kint κ Δ' with
      | eq_refl => applyAll (map (intP η) ζ)
      end (interp τ η).
  Proof.
    revert κᵣ τ EQ; induction ζ as [| [κₐ σ]]; intros; simpl; subst.
    - now rewrite UIP_refl with (p := fkm_intP nil η eq_refl).
    - specialize (IHζ _ (τ σ) eq_refl); simpl in IHζ; rewrite IHζ; clear IHζ.
      fold (fkind κ ζ); simpl.
      generalize (fkm_intP ζ η (eq_refl (x := fkind κ ζ))) as EQ.
      generalize (fkm_intP (existT _ κₐ σ :: ζ) η (eq_refl (x := κₐ ⇒ fkind κ ζ))) as EQ'.
      simpl in *; revert τ.
      generalize (fkind κ ζ); intros; subst.
      now rewrite UIP_refl with (p := EQ').
  Qed.

  Lemma xxx κ (ζ₁ : list (sigT (λ κ, Nf κ ε))) ζ₂ (ν : Neu (fkind κ ζ₁) ε) EQ₁ EQ₂ :
    view ν (map (mapT (@mkArg)) ζ₁ ++ ζ₂) EQ₁ = view (applyAll (F := λ κ, Neu κ ε) ζ₁ ν) ζ₂ EQ₂.
  Proof.
    induction ζ₁ as [| [κ' μ]]; simpl in *.
    - f_equal; apply UIP.
    - inversion EQ₁ as [EQ₃].
      rewrite <- IHζ₁ with (EQ₁ := EQ₃); simpl.
      f_equal; apply UIP.
  Qed.

  Lemma yyy (ζ : list (sigT (λ κ, kint κ ε))) (ν : Neu (fkind ⋆ ζ) ε) :
    applyAll (F := λ κ, kint κ ε) ζ (reflect ν) =
      match fkind_map (λ κ, reify) _ _ ζ eq_refl in _ = κ return neu ε κ → neu ε ⋆ with
    | eq_refl => applyAll (F := λ κ, Neu κ ε) (map (mapT (λ κ, @reify κ _)) ζ)
    end ν.
  Proof.
    revert ν; induction ζ as [| [κ' μ]]; intros; simpl in *.
    - now rewrite UIP_refl with (p := fkind_map (λ κ : Kinds.kind, reify) ⋆ _ nil eq_refl).
    - foldArrs; rewrite map_id'; rewrite IHζ; clear IHζ.
      generalize (fkind_map (λ κ, reify) _ ⋆ (existT _ κ' μ :: ζ)
                    (eq_refl (x := κ' ⇒ (fkind ⋆ ζ)))) as EQ'.
      generalize (fkind_map (λ κ, reify) (fkind _ ζ) ⋆ ζ eq_refl) as EQ; simpl.
      revert ν.
      generalize (fkind ⋆ ζ) as κ; intros; subst.
      now rewrite UIP_refl with (p := EQ').
  Qed.

  Definition eqSI (p₁ p₂ : sigT (λ κ, kint κ ε)) :=
    let (κ₁, μ₁) := p₁ in
    let (κ₂, μ₂) := p₂ in
    ∃ (EQ : κ₁ = κ₂), μ₁ ≅ eq_rect_r (λ κ, kint κ ε) μ₂ EQ.

  Lemma applyAllI_eq ζ₁ ζ₂ (μ₁ μ₂ : kint _ ε) (EQ : fkind ⋆ ζ₁ = fkind ⋆ ζ₂)
    (EQμ : μ₁ ≅ eq_rect_r (λ κ, kint κ ε) μ₂ EQ) (EQζ : Forall2 eqSI ζ₁ ζ₂) :
    applyAll ζ₁ μ₁ = applyAll ζ₂ μ₂.
  Proof.
    revert μ₁ μ₂ EQ EQμ; induction EQζ; intros; simpl in *.
    - rewrite UIP_refl with (p := EQ) in EQμ; exact EQμ.
    - destruct x as [κ ν₁], y as [κ' ν₂], H as [EQκ EQν]; subst κ'; simpl in *.
      inversion EQ as [EQ']; eapply IHEQζ with (EQ := EQ'); clear IHEQζ EQζ.
      revert EQ μ₂ EQμ EQ'; unfold eq_rect_r in EQν; simpl in EQν.
      fold kint; fold @fkind; generalize (fkind ⋆ l') as κ'; intros.
      subst κ'; rewrite UIP_refl with (p := EQ) in EQμ; unfold eq_rect_r in *; simpl in *.
      now rewrite EQμ, EQν.
  Qed.

  Fixpoint argify κ (μ : Nf κ ε) : unArg κ (mkArg μ) = μ
  with viewify κ (ν : Neu κ ε) : ∀ η (EQ : fkind ⋆ η = κ),
      unView (view ν η EQ) =
        applyAll (map (mapT unArg) η) (eq_rect_r (λ κ, Neu κ ε) ν (fkind_map unArg _ _ η EQ)).
  Proof.
    - destruct μ; simpl; f_equal.
      rewrite viewify; simpl; unfold eq_rect_r.
      now rewrite UIP_refl with
        (p := @eq_sym _ ⋆ ⋆ (fkind_map unArg ⋆ ⋆ nil (@eq_refl _ ⋆))).
    - intros; destruct ν; simpl.
      + destruct x.
      + rewrite viewify; simpl; f_equal; subst; fold @fkind.
        generalize (fkind_map unArg (fkind ⋆ η) ⋆ η eq_refl) as EQ.
        generalize (fkind_map unArg (κₐ ⇒ (fkind ⋆ η)) ⋆
                      (existT _ κₐ (@mkArg κₐ μ) :: η)
                      (f_equal (KArr κₐ) (@eq_refl _ (fkind ⋆ η)))) as EQ'; simpl.
        revert ν; generalize (fkind ⋆ η) as κ; intros; subst.
        rewrite UIP_refl with (p := EQ'); unfold eq_rect_r; simpl.
        f_equal; apply argify.
      + clear; destruct c.
        * destruct η; [| discriminate]; simpl in *.
          rewrite UIP_refl with (p := fkind_map unArg ⋆ ⋆ nil EQ),
              UIP_refl with (p := EQ); unfold eq_rect_r; now simpl.
        * destruct η; [| discriminate]; simpl in *.
          rewrite UIP_refl with (p := fkind_map unArg ⋆ ⋆ nil EQ),
              UIP_refl with (p := EQ); unfold eq_rect_r; now simpl.
        * destruct η as [| [κ₁ ν₁] [| [κ₂ ν₂] [|]]]; [discriminate .. | | discriminate].
          inversion EQ; subst; simpl in *.
          rewrite UIP_refl with
            (p := fkind_map unArg _ ⋆
                    (existT _ ⋆ ν₁ :: existT _ ⋆ ν₂ :: nil) EQ),
              UIP_refl with (p := EQ); now simpl.
        * destruct η as [| [κ₁ ν₁] [| [κ₂ ν₂] [|]]]; [discriminate .. | | discriminate].
          inversion EQ; subst; simpl in *.
          rewrite UIP_refl with
            (p := fkind_map unArg _ ⋆
                    (existT _ ⋆ ν₁ :: existT _ ⋆ ν₂ :: nil) EQ),
              UIP_refl with (p := EQ); now simpl.
        * destruct η as [| [κ₁ ν₁] [| [κ₂ ν₂] [|]]]; [discriminate .. | | discriminate].
          inversion EQ; subst; simpl in *.
          rewrite UIP_refl with
            (p := fkind_map unArg _ ⋆
                    (existT _ ⋆ ν₁ :: existT _ ⋆ ν₂ :: nil) EQ),
              UIP_refl with (p := EQ); now simpl.
        * destruct η as [| [κ' ν] [|]]; [discriminate | | discriminate].
          inversion EQ; subst; simpl in *.
          rewrite UIP_refl with
            (p := fkind_map unArg _ ⋆
                    (existT _ (κ ⇒ ⋆) ν :: nil) EQ),
              UIP_refl with (p := EQ); now simpl.
        * destruct η as [| [κ' ν] [|]]; [discriminate | | discriminate].
          inversion EQ; subst; simpl in *.
          rewrite UIP_refl with
            (p := fkind_map unArg _ ⋆
                    (existT _ (κ ⇒ ⋆) ν :: nil) EQ),
              UIP_refl with (p := EQ); now simpl.
        * destruct η as [| [κ' ν]]; [discriminate |]; inversion EQ; subst; simpl in *.
          rewrite UIP_refl with (p := EQ); simpl; clear EQ.
          destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂];
            rewrite UIP_refl with (p := EQ₂), UIP_refl with (p := EQ₁); simpl; clear.
          generalize (fkind_map unArg (fkind ⋆ η) ⋆ η eq_refl) as EQ.
          generalize (fkind_map unArg
                        ((fkind ⋆ η ⇒ fkind ⋆ η) ⇒ fkind ⋆ η) ⋆
                        (existT _ (fkind ⋆ η ⇒ fkind ⋆ η) ν :: η)
                        (@eq_refl Kinds.kindEqDec.U
                           ((fkind ⋆ η ⇒ fkind ⋆ η) ⇒ fkind ⋆ η))) as EQ'; simpl in *.
          revert ν; generalize (fkind ⋆ η) as κ; intros; subst; simpl.
          rewrite UIP_refl with (p := EQ'); unfold eq_rect_r; now simpl.
      + destruct η; [| discriminate]; simpl in *.
        rewrite UIP_refl with (p := fkind_map unArg ⋆ ⋆ nil EQ).
        unfold eq_rect_r; simpl; f_equal.
        apply (argify ⋆).
      + destruct η; [| discriminate]; simpl in *.
        rewrite UIP_refl with (p := fkind_map unArg ⋆ ⋆ nil EQ).
        unfold eq_rect_r; simpl; f_equal.
        apply (argify ⋆).
      + destruct η; [| discriminate]; simpl in *.
        rewrite UIP_refl with (p := fkind_map unArg ⋆ ⋆ nil EQ).
        unfold eq_rect_r; simpl; f_equal.
  Qed.

End GView.
