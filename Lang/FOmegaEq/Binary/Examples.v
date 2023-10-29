Require Import Utf8.
Require Import IxFree.Lib.
Require Import List.
Require Import Binding.Lib Binding.Set Binding.Intrinsic.
Require Binding.Env.
Require Import FOmegaEq.Binary.Realize FOmegaEq.Types FOmegaEq.Syntax
  FOmegaEq.Interp FOmegaEq.Universe FOmegaEq.Binary.Compat FOmegaEq.Binary.Realize
  FOmegaEq.Binary.Soundness FOmegaEq.Typing FOmegaEq.OpSemantics FOmegaEq.Presheaves.
Require FOmegaEq.Kinds.
Import -(notations) Kinds.
Import Kinds.DED_kind.
Require Import Morphisms.

Section Core.

  Definition fix_comb {V} : value V
    := (Λ (ƛ (ƛ e_unroll (v_var VZ)
                >>= v_var VZ (v_var (VS VZ))
                >>= v_var (VS (VS (VS VZ))) (v_var VZ))
             (v_roll (ƛ e_unroll (v_var VZ)
                        >>= v_var VZ (v_var (VS VZ))
                        >>= v_var (VS (VS (VS VZ))) (v_var VZ)))))%syn.

  Fact fix_comb_typ {V Δ Ξ Γ} : typing_val Δ Ξ Γ (@fix_comb V) (∀ᵗ KTyp , ((0ᵛ →ᵗ 0ᵛ) →ᵗ 0ᵛ))%typ.
  Proof.
    apply T_tlam, T_val, T_lam.
    apply T_app with
      (rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl)))%typ.
    - apply T_lam.
      apply T_bind with
        ((rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl))) →ᵗ 0ᵛ)%typ.
      + apply T_unroll with KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl))%typ
                            (rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl)))%typ.
        * term_simpl.
          apply rel_app_refl.
        * apply T_var.
          term_simpl.
          reflexivity.
      + apply T_bind with 0ᵛ.
        * apply T_app with (rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl)))%typ.
          -- apply T_var.
             term_simpl.
             reflexivity.
          -- apply T_var.
             term_simpl.
             reflexivity.
        * apply T_app with 0ᵛ.
          -- apply T_var.
             term_simpl.
             reflexivity.
          -- apply T_var.
             term_simpl.
             reflexivity.
    - apply T_roll with KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl))%typ
                        ((rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl))) →ᵗ 0ᵛ)%typ.
      + term_simpl.
        apply rel_app_refl.
      + apply T_lam.
        apply T_bind with ((rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl))) →ᵗ 0ᵛ)%typ.
        * apply T_unroll with KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl))%typ
                              (rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl)))%typ.
          -- term_simpl.
             apply rel_app_refl.
          -- apply T_var.
             term_simpl.
             reflexivity.
        * apply T_bind with 0ᵛ.
          -- apply T_app with (rec_type (Δ ▹ KTyp) KTyp (0ᵛ →ᵗ (@t_var (Δ ▹ KTyp ▹ KTyp) KTyp (VS VZ) eq_refl)))%typ.
             ++ apply T_var.
                term_simpl.
                reflexivity.
             ++ apply T_var.
                term_simpl.
                reflexivity.
          -- apply T_app with 0ᵛ.
             ++ apply T_var.
                term_simpl.
                reflexivity.
             ++ apply T_var.
                term_simpl.
                reflexivity.
  Qed.

  Definition composition {X : Set} : value X
    := (Λ Λ Λ ƛ ƛ ƛ (((v_var (VS VZ)) (v_var VZ)) >>= ((v_var (VS (VS (VS VZ)))) (v_var VZ))))%syn.

  Fact composition_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ}
    : Δ ∣ Ψ ∣ Γ ⊢ᵥ composition : ∀ᵗ KTyp, ∀ᵗ KTyp, ∀ᵗ KTyp, ((t_var _ (VS VZ : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl) →ᵗ 0ᵛ)
                                                              →ᵗ ((t_var _ (VS (VS VZ) : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl) →ᵗ (t_var _ (VS VZ : dom (_ ▹ _ ▹ _)) eq_refl))
                                                              →ᵗ ((t_var _ (VS (VS VZ) : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl) →ᵗ 0ᵛ).
  Proof.
    do 11 constructor.
    econstructor.
    - eapply T_app.
      + constructor; reflexivity.
      + constructor; reflexivity.
    - eapply T_app.
      + constructor; reflexivity.
      + constructor; reflexivity.
  Qed.

  Definition bind_app {X : Set} (e₁ e₂ : expr X) : expr X
    := (e₁ >>= (shift e₂ >>= (v_var (VS VZ) (v_var VZ))))%syn.

  Fact bind_app_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} {e₁ e₂ : expr X} {τ₁ τ₂ : typ KTyp Δ}
    : Δ ∣ Ψ ∣ Γ ⊢ₑ e₁ : τ₁ →ᵗ τ₂ -> Δ ∣ Ψ ∣ Γ ⊢ₑ e₂ : τ₁ -> Δ ∣ Ψ ∣ Γ ⊢ₑ bind_app e₁ e₂ : τ₂.
  Proof.
    intros HT1 HT2.
    eapply T_bind.
    - apply HT1.
    - eapply T_bind.
      + apply typing_shift_exp, HT2.
      + eapply T_app.
        * constructor; reflexivity.
        * constructor; reflexivity.
  Qed.

  Definition loop {X} : expr X
    := e_bind (v_fix ((v_var (VS VZ)) (v_var VZ)) v_unit) (e_abort (v_var VZ)).

  Fact loop_typ {X Δ Ψ Γ τ} : @typing_expr X Δ Ψ Γ loop τ.
  Proof.
    apply T_bind with ⊥%U.
    - apply T_app with ⊤%U.
      + apply T_rec.
        apply T_app with ⊤%U.
        * apply T_var; reflexivity.
        * apply T_var; reflexivity.
      + constructor.
    - constructor.
      apply T_var; reflexivity.
  Qed.

  Lemma ECL_loop {P e n} : n ⊨ ECL P loop e.
  Proof.
    loeb_induction.
    eapply ECL_step'; [constructor; constructor | econstructor 1 |].
    later_shift.
    term_simpl.
    apply IH.
  Qed.

End Core.

Section Nat.

  Definition Nat {Δ} : typ KTyp Δ
    := rec_type Δ KTyp (⊤ + 0ᵛ)%typ.

  Definition Z {X : Set} : value X
    := v_roll (v_inj L ⟨⟩%syn).

  Definition S {X : Set} : value X -> value X
    := fun n => v_roll (v_inj R n).

  Fact Z_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ Z : Nat.
  Proof.
    eapply T_roll.
    apply rel_app_refl.
    term_simpl.
    do 2 constructor.
  Qed.

  Fact S_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} {n} : Δ ∣ Ψ ∣ Γ ⊢ᵥ n : Nat ->
                  Δ ∣ Ψ ∣ Γ ⊢ᵥ (S n) : Nat.
  Proof.
    intros HT.
    eapply T_roll.
    apply rel_app_refl.
    term_simpl.
    constructor; assumption.
  Qed.

  Definition Z' {Δ} : typ KTyp Δ
    := ⊥%typ.

  Definition S' {Δ} : typ (KArr KTyp KTyp) Δ
    := (ƛ (0ᵛ + ⊤))%typ.

End Nat.

Section ReprSpec.

  Definition ReprSpec {Δ} τ : typ KTyp Δ
    := (∃ᵗ KTyp , (0ᵛ →ᵗ τ) × (τ →ᵗ 0ᵛ))%typ.

End ReprSpec.

Section GTree.

  Definition GTreeNat {Δ} : typ (KArr KTyp KTyp) Δ
    := rec_type Δ (KArr KTyp KTyp)
         (ƛ (((0ᵛ ≃ Z') →ᶜ ⊤)
             + (∃ᵗ KTyp , ((t_var _ (VS VZ : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl) ≃ S' 0ᵛ)
                            ×ᶜ ((t_var _ (VS (VS VZ) : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl) 0ᵛ)
                            × Nat
                            × ((t_var _ (VS (VS VZ) : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl) 0ᵛ))))%typ.

  Definition GTreeNatAbstract {Δ} : typ KTyp Δ
    := (∃ᵗ KTyp , GTreeNat 0ᵛ)%typ.

End GTree.

Section PhantomRepr.

  Definition Repr {Δ} : typ (KArr KTyp KTyp) Δ
    := (ƛ (((0ᵛ ≃ Nat) ×ᶜ Nat)
           + ((0ᵛ ≃ ⊤) ×ᶜ ⊤)))%typ.

  Definition repr_nat {X} : value X
    := (ƛ (((v_inj L ⟨ (v_var VZ) ⟩ᶜ))))%syn.

  Fact repr_nat_typ {X Δ Ψ Γ} : typing_val Δ Ψ Γ (@repr_nat X) (Nat →ᵗ Repr Nat)%typ.
  Proof.
    constructor.
    eapply T_congE.
    apply tpi_symm.
    apply tpi_beta.
    constructor.
    apply T_injl.
    term_simpl.
    eapply T_withC.
    - apply T_var.
      term_simpl.
      reflexivity.
    - apply Equiv_tproves.
  Qed.

  Definition repr_unit {X} : value X
    := (ƛ (((v_inj R ⟨ (v_var VZ) ⟩ᶜ))))%syn.

  Fact repr_unit_typ {X Δ Ψ Γ} : typing_val Δ Ψ Γ (@repr_unit X) (⊤ →ᵗ Repr ⊤)%typ.
  Proof.
    constructor.
    eapply T_congE.
    apply tpi_symm.
    apply tpi_beta.
    constructor.
    apply T_injr.
    term_simpl.
    eapply T_withC.
    - apply T_var.
      term_simpl.
      reflexivity.
    - apply Equiv_tproves.
  Qed.

  Definition repr_nat_unpack {X} : value X
    := (ƛ (e_case (v_var VZ) (e_lwith (v_var VZ) (v_var VZ)) (e_lwith (v_var VZ) (e_cabort))))%syn.

  Fact repr_nat_unpack_typ {X Δ Ψ Γ} : typing_expr Δ Ψ Γ (@repr_nat_unpack X) (Repr Nat →ᵗ Nat)%typ.
  Proof.
    unshelve eapply T_congE.
    apply (((Nat ≃ Nat) ×ᶜ Nat)
           + ((Nat ≃ ⊤) ×ᶜ ⊤) →ᵗ Nat)%typ.
    apply tpi_app; [| apply Equiv_tproves].
    apply tpi_app; [apply tpi_ctor |].
    apply tpi_symm.
    eapply tpi_trans.
    apply tpi_beta.
    term_simpl.
    apply Equiv_tproves.
    do 2 constructor.
    eapply T_case with (τ₁ := ((Nat ≃ Nat) ×ᶜ Nat)%typ)
                       (τ₂ := ((Nat ≃ ⊤) ×ᶜ ⊤)%typ).
    - eapply T_lwith.
      + apply T_var; reflexivity.
      + constructor.
        apply T_var; reflexivity.
    - eapply T_lwith.
      + apply T_var; reflexivity.
      + eapply T_cabort.
        * apply tpi_ax; constructor; reflexivity.
        * eapply td_ctd.
          do 2 econstructor.
          econstructor.
          unfold cdiscrK.
          destruct (kindEqDec.eq_dec (KArr (KArr KTyp KTyp) KTyp) KTyp) as [H | H].
          inversion H.
          apply I.
    - apply T_var; reflexivity.
  Qed.

End PhantomRepr.

Section TermRepr.

  Definition φ₁ {Δ} : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp ▹ KTyp)
    := t_var _ ((VS (VS (VS VZ))) : dom (_ ▹ _ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition α₁ {Δ} : typ KTyp (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp ▹ KTyp)
    := t_var _ ((VS (VS VZ)) : dom (_ ▹ _ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition β₁ {Δ} : typ KTyp (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp ▹ KTyp)
    := t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition γ₁ {Δ} : typ KTyp (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp ▹ KTyp)
    := t_var _ (VZ : dom (_ ▹ _ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition φ₂ {Δ} : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp)
    := t_var _ ((VS (VS VZ)) : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition α₂ {Δ} : typ KTyp (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp)
    := t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition β₂ {Δ} : typ KTyp (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp)
    := t_var _ (VZ : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition Term {Δ} : typ (KArr KTyp KTyp) Δ
    := rec_type Δ (KArr KTyp KTyp)
         (ƛ (0ᵛ
             + (∃ᵗ KTyp , ∃ᵗ KTyp , ((α₁ ≃ β₁ →ᵗ γ₁) ×ᶜ (β₁ →ᵗ (φ₁ γ₁))))
             + (∃ᵗ KTyp , (φ₂ (β₂ →ᵗ α₂)) × (φ₂ β₂))))%typ.

  Definition inj {X} : value X
    := (Λ ƛ (e_val (v_roll (v_inj L (v_inj L (v_var VZ))))))%syn.

  Fact inj_typ {X Δ Ψ Γ} : typing_val Δ Ψ Γ (@inj X) (∀ᵗ KTyp , 0ᵛ →ᵗ Term 0ᵛ)%typ.
  Proof.
    do 4 constructor.
    eapply T_roll.
    apply rel_app_app, rel_app_refl.
    match goal with
    | |- context G [subst _ ?a] => set (φ := a)
    end.
    clearbody φ.
    term_simpl.
    eapply T_congV.
    apply tpi_symm.
    apply tpi_beta.
    term_simpl.
    do 2 apply T_injl.
    apply T_var.
    term_simpl.
    reflexivity.
  Qed.

  Definition applyTerm {X} : value X
    := (Λ (Λ (ƛ (ƛ (e_val (v_roll (v_inj R (v_pack (v_pair (v_var (VS VZ)) (v_var VZ))))))))))%syn.

  Fact applyTerm_typ {X Δ Ψ Γ} : typing_val Δ Ψ Γ (@applyTerm X)
                                   (∀ᵗ KTyp , ∀ᵗ KTyp ,
                                      Term (0ᵛ →ᵗ (t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _)) eq_refl)) →ᵗ
                                        Term 0ᵛ →ᵗ
                                        Term (t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _)) eq_refl))%typ.
  Proof.
    do 8 constructor.
    eapply T_roll.
    apply rel_app_app, rel_app_refl.
    match goal with
    | |- context G [subst _ ?a] => set (φ := a)
    end.
    term_simpl.
    eapply T_congV.
    apply tpi_symm.
    apply tpi_beta.
    term_simpl.
    apply T_injr.
    apply T_pack with 0ᵛ.
    term_simpl.
    apply T_pair.
    - apply T_var.
      simpl.
      reflexivity.
    - apply T_var.
      simpl.
      reflexivity.
  Qed.

  Definition funTerm {X} : value X
    := (Λ (Λ (ƛ (e_val (v_roll (v_inj L (v_inj R (v_pack (v_pack (⟨ v_var VZ ⟩ᶜ))))))))))%syn.

  Fact funTerm_typ {X Δ Ψ Γ} : typing_val Δ Ψ Γ (@funTerm X)
                                 (∀ᵗ KTyp , ∀ᵗ KTyp ,
                                    ((t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ Term 0ᵛ) →ᵗ
                                      Term ((t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ 0ᵛ))%typ.
  Proof.
    do 6 constructor.
    eapply T_roll.
    apply rel_app_app, rel_app_refl.
    match goal with
    | |- context G [subst _ ?a] => set (φ := a)
    end.
    term_simpl.
    eapply T_congV.
    apply tpi_symm.
    apply tpi_beta.
    term_simpl.
    apply T_injl, T_injr.
    apply T_pack with (t_var _ ((VS VZ) : dom (_ ▹ _ ▹ _)) eq_refl).
    term_simpl.
    apply T_pack with 0ᵛ.
    term_simpl.
    apply T_withC.
    - apply T_var.
      simpl.
      reflexivity.
    - apply Equiv_tproves.
  Qed.

  Program Definition evalTerm' {X} : value X
    := (ƛ ƛ Λ ƛ (e_bind (e_unroll (v_var VZ)) (e_case (v_var VZ)
                                               (e_case (v_var VZ)
                                                  ((v_var VZ))
                                                  (e_unpack (v_var VZ)
                                                     (e_unpack (v_var VZ)
                                                        (e_lwith (v_var VZ) (v_lam _)))))
                                               (e_unpack (v_var VZ) _))))%syn.
  Next Obligation.
    apply (e_bind (e_app (v_var (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))) v_unit)).
    apply (e_bind (e_tapp (v_var VZ))).
    apply (e_bind (e_app (v_var (VS (VS (VS VZ)))) (v_var (VS (VS VZ))))).
    apply (e_app (v_var (VS VZ)) (v_var VZ)).
  Defined.
  Next Obligation.
    apply (e_bind (e_proj L (v_var VZ))).
    apply (e_bind (e_proj R (v_var (VS VZ)))).
    apply (e_bind (e_app (v_var (VS (VS (VS (VS (VS (VS (VS VZ)))))))) v_unit)).
    apply (e_bind (e_tapp (v_var VZ))).
    apply (e_bind (e_tapp (v_var (VS VZ)))).
    apply (e_bind (e_app (v_var (VS VZ)) (v_var (VS (VS (VS (VS VZ))))))).
    apply (e_bind (e_app (v_var (VS VZ)) (v_var (VS (VS (VS (VS VZ))))))).
    apply (e_app (v_var (VS VZ)) (v_var VZ)).
  Defined.

  Fact evalTerm'_typ {X Δ Ψ Γ} : @typing_val X Δ Ψ Γ ((@evalTerm' X))
                                   ((tc_unit →ᵗ ∀ᵗ KTyp , Term 0ᵛ →ᵗ 0ᵛ)%typ →ᵗ
                                      (tc_unit →ᵗ (∀ᵗ KTyp , Term 0ᵛ →ᵗ 0ᵛ)))%typ.
  Proof.
    do 7 constructor.
    set (α := 0ᵛ).
    set (body := (ƛ 0ᵛ + (∃ᵗ KTyp, (∃ᵗ KTyp, (α₁ ≃ β₁ →ᵗ γ₁) ×ᶜ (β₁ →ᵗ φ₁ γ₁))) +
                    (∃ᵗ KTyp, φ₂ (β₂ →ᵗ α₂) × φ₂ β₂))%typ : typ (KArr KTyp KTyp) (Δ ▹ KTyp ▹ KArr KTyp KTyp)).
    set (recBody := subst body Term).
    apply T_bind with (recBody α).
    - eapply T_unroll.
      apply rel_app_app, rel_app_refl.
      apply T_var; term_simpl; reflexivity.
    - set (α' := (t_var KTyp (VS (VS VZ) : dom (Δ ▹ KTyp ▹ KTyp ▹ KTyp)) eq_refl)).
      set (α'' := (t_var KTyp (VS VZ : dom (Δ ▹ KTyp ▹ KTyp)) eq_refl)).
      set (β' := (t_var KTyp (VS VZ : dom (Δ ▹ KTyp ▹ KTyp ▹ KTyp)) eq_refl)).
      apply T_case with
        ((0ᵛ) + (∃ᵗ KTyp, (∃ᵗ KTyp, (α' ≃ β' →ᵗ 0ᵛ) ×ᶜ (β' →ᵗ Term 0ᵛ))))%typ
        (∃ᵗ KTyp, Term (0ᵛ →ᵗ α'') × Term 0ᵛ)%typ.
      + apply T_case with
          ((0ᵛ))%typ
          (∃ᵗ KTyp, (∃ᵗ KTyp, (α' ≃ β' →ᵗ 0ᵛ) ×ᶜ (β' →ᵗ Term 0ᵛ)))%typ.
        * apply T_val, T_var; simpl; reflexivity.
        * apply T_unpack with KTyp (∃ᵗ KTyp, (α' ≃ β' →ᵗ 0ᵛ) ×ᶜ (β' →ᵗ Term 0ᵛ))%typ.
          -- apply T_var; term_simpl; reflexivity.
          -- apply T_unpack with KTyp ((α' ≃ β' →ᵗ 0ᵛ) ×ᶜ (β' →ᵗ Term 0ᵛ))%typ.
             ++ apply T_var; term_simpl; reflexivity.
             ++ apply T_lwith with
                  (α' ≃ β' →ᵗ 0ᵛ)%typ
                  (β' →ᵗ Term 0ᵛ)%typ.
                ** apply T_var; term_simpl; reflexivity.
                ** apply T_val.
                   apply T_congV with (β' →ᵗ 0ᵛ)%typ.
                   --- subst α α'.
                       term_simpl.
                       apply tpi_symm, tpi_ax; constructor.
                       reflexivity.
                   --- constructor.
                       unfold evalTerm'_obligation_1.
                       apply T_bind with (∀ᵗ KTyp , Term 0ᵛ →ᵗ 0ᵛ)%typ.
                       +++ eapply T_app.
                           apply T_var; simpl; reflexivity.
                           constructor.
                       +++ apply T_bind with (Term 0ᵛ →ᵗ 0ᵛ)%typ.
                           *** eapply T_congE.
                               2: apply T_tapp, T_var; reflexivity.
                               term_simpl.
                               apply Equiv_tproves.
                           *** apply T_bind with (Term 0ᵛ).
                               ---- apply T_app with β'.
                                    apply T_var; reflexivity.
                                    apply T_var; reflexivity.
                               ---- apply T_app with (Term 0ᵛ).
                                    apply T_var; reflexivity.
                                    apply T_var; reflexivity.
        * apply T_var; term_simpl; reflexivity.
      + apply T_unpack with KTyp (Term (0ᵛ →ᵗ α'') × Term 0ᵛ)%typ.
        * apply T_var; term_simpl; reflexivity.
        * apply T_bind with (Term (0ᵛ →ᵗ α''))%typ.
          apply T_projL with (Term 0ᵛ).
          apply T_var; term_simpl; reflexivity.
          apply T_bind with (Term 0ᵛ).
          apply T_projR with (Term (0ᵛ →ᵗ α''))%typ.
          apply T_var; term_simpl; reflexivity.
          eapply T_bind.
          -- apply T_app with ⊤%U.
             apply T_var; simpl.
             reflexivity.
             constructor.
          -- apply T_bind with (Term (0ᵛ →ᵗ α'') →ᵗ (0ᵛ →ᵗ α''))%typ.
             ++ eapply T_congE.
                2: apply T_tapp, T_var; reflexivity.
                term_simpl.
                apply Equiv_tproves.
             ++ apply T_bind with (Term 0ᵛ →ᵗ 0ᵛ)%typ.
                ** eapply T_congE.
                   2: apply T_tapp, T_var; reflexivity.
                   term_simpl.
                   apply Equiv_tproves.
                ** apply T_bind with (0ᵛ →ᵗ α'')%typ.
                   --- eapply T_app.
                       apply T_var; term_simpl; reflexivity.
                       apply T_var; term_simpl; reflexivity.
                   --- apply T_bind with 0ᵛ.
                       +++ apply T_app with (Term 0ᵛ).
                           apply T_var; reflexivity.
                           apply T_var; reflexivity.
                       +++ apply T_app with 0ᵛ.
                           *** apply T_var; reflexivity.
                           *** apply T_var; term_simpl; reflexivity.
      + eapply T_congV.
        2: apply T_var; term_simpl; reflexivity.
        eapply tpi_trans.
        apply tpi_beta.
        term_simpl.
        apply Equiv_tproves.
  Qed.

  Definition fixpoint {X} : value X
    := v_fix (e_bind ((shift (shift (evalTerm'))) (v_var (VS VZ))) ((v_var VZ) (v_var (VS VZ)))).

  Fact fixpoint_typ {V Δ Ξ Γ}
    : typing_val Δ Ξ Γ (@fixpoint V) (tc_unit →ᵗ ∀ᵗ KTyp , Term 0ᵛ →ᵗ 0ᵛ)%typ.
  Proof.
    simpl.
    apply T_rec.
    eapply T_bind.
    apply T_app with (tc_unit →ᵗ ∀ᵗ KTyp , Term 0ᵛ →ᵗ 0ᵛ)%typ.
    do 2 apply typing_shift_val.
    apply evalTerm'_typ.
    apply T_var; simpl; reflexivity.
    apply T_app with ⊤%U.
    apply T_var; simpl; reflexivity.
    apply T_var; simpl; reflexivity.
  Qed.

  Definition fixpoint' {X} : value X
    := (ƛ (e_bind (fixpoint v_unit) (e_bind (e_tapp (v_var VZ)) ((v_var VZ) (v_var (VS (VS VZ)))))))%syn.

  Fact fixpoint'_typ {X Δ Ξ Γ} τ
    : typing_val Δ Ξ Γ (@fixpoint' X) (Term τ →ᵗ τ)%typ.
  Proof.
    constructor.
    apply T_bind with (∀ᵗ KTyp , Term 0ᵛ →ᵗ 0ᵛ)%typ.
    apply T_app with ⊤%U.
    apply fixpoint_typ.
    constructor.
    apply T_bind with (Term τ →ᵗ τ)%typ.
    eapply T_congE.
    2: apply T_tapp, T_var; reflexivity.
    term_simpl.
    apply Equiv_tproves.
    apply T_app with (Term τ).
    apply T_var; simpl; reflexivity.
    apply T_var; simpl; reflexivity.
  Qed.

  Definition inj' {X} : value X
    := (ƛ (e_bind (e_tapp inj)) ((v_var VZ) (v_var (VS VZ))))%syn.

End TermRepr.

Section ListRec.

  Definition φlist {Δ} : typ KTyp (Δ ▹ KTyp)
    := t_var _ (VZ : dom (_ ▹ _)) eq_refl.

  Definition List {Δ} (τ : typ KTyp Δ) : typ KTyp Δ
    := rec_type Δ KTyp
         ((⊤ + (shift τ × φlist)))%typ.

  Definition ListHead {X} : value X
    := (ƛ e_bind (e_unroll (v_var VZ)) (e_case (v_var VZ) loop (e_proj L (v_var VZ))))%syn.

  Fact ListHead_typ {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ ListHead (List τ →ᵗ τ)%typ.
  Proof.
    constructor.
    set (body := (⊤ + (shift τ × (t_var _ (VZ : dom (Δ ▹ _)) eq_refl)))%typ).
    set (recBody := subst body (List τ)).
    apply T_bind with recBody.
    - eapply T_unroll.
      apply rel_app_refl.
      apply T_var; reflexivity.
    - unfold recBody.
      term_simpl.
      apply T_case with ⊤%U (τ × (List τ))%typ.
      + apply loop_typ.
      + apply T_projL with (List τ).
        apply T_var; reflexivity.
      + apply T_var; reflexivity.
  Qed.

  Definition ListNil {X} : value X
    := (v_roll (v_inj L v_unit))%syn.

  Fact ListNil_typ {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ ListNil (List τ).
  Proof.
    set (body := (⊤ + (shift τ × (t_var _ (VZ : dom (Δ ▹ _)) eq_refl)))%typ).
    set (recBody := subst body (List τ)).
    eapply T_roll.
    eapply rel_app_refl.
    term_simpl.
    do 2 constructor.
  Qed.

  Definition ListInj {X} : value X
    := (ƛ v_roll (v_inj R (v_pair (v_var VZ) ListNil)))%syn.

  Fact ListInj_typ {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ ListInj (τ →ᵗ List τ)%typ.
  Proof.
    set (body := (⊤ + (shift τ × (t_var _ (VZ : dom (Δ ▹ _)) eq_refl)))%typ).
    set (recBody := subst body (List τ)).
    do 2 constructor.
    eapply T_roll.
    eapply rel_app_refl.
    term_simpl.
    do 2 constructor.
    - apply T_var; reflexivity.
    - apply ListNil_typ.
  Qed.

  Definition ListCons {X} : value X
    := (ƛ ƛ v_roll (v_inj R (v_pair (v_var (VS VZ)) (v_var VZ))))%syn.

  Fact ListCons_typ {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ ListCons (τ →ᵗ List τ →ᵗ List τ)%typ.
  Proof.
    set (body := (⊤ + (shift τ × (t_var _ (VZ : dom (Δ ▹ _)) eq_refl)))%typ).
    set (recBody := subst body (List τ)).
    do 4 constructor.
    eapply T_roll.
    eapply rel_app_refl.
    term_simpl.
    do 2 constructor.
    - apply T_var; reflexivity.
    - apply T_var; reflexivity.
  Qed.

  Definition ListTail {X} : value X
    := (ƛ e_bind
          (e_unroll (v_var VZ))
          (e_case (v_var VZ)
             ListNil
             (e_proj R (v_var VZ))))%syn.

  Fact ListTail_typ {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ ListTail (List τ →ᵗ List τ)%typ.
  Proof.
    set (body := (⊤ + (shift τ × (t_var _ (VZ : dom (Δ ▹ _)) eq_refl)))%typ).
    set (recBody := subst body (List τ)).
    constructor.
    eapply T_bind.
    eapply T_unroll.
    eapply rel_app_refl.
    apply T_var; reflexivity.
    eapply T_case.
    - apply T_val, ListNil_typ.
    - eapply T_projR.
      term_simpl.
      apply T_var; reflexivity.
    - apply T_var; reflexivity.
  Qed.

  Definition ListMap {X : Set} : value X :=
    (Λ Λ ƛ (e_val (v_fix (e_unroll (v_var VZ) >>=
                            e_case (v_var VZ)
                            ListNil
                            ((e_proj L (v_var VZ)) >>=
                               (e_proj R (v_var (VS VZ))) >>=
                               ((v_var (VS (VS (VS (VS (VS (VS VZ))))))) (v_var (VS VZ))) >>=
                               ListCons (v_var VZ) >>=
                               (v_var (VS (VS (VS (VS (VS (VS (VS VZ))))))) (v_var (VS (VS VZ)))) >>=
                               (v_var (VS VZ)) (v_var VZ))))))%syn.

  Fact ListMap_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ}
    : Δ ∣ Ψ ∣ Γ ⊢ᵥ ListMap : ∀ᵗ KTyp , ∀ᵗ KTyp , ((t_var _ (VS VZ : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ 0ᵛ) →ᵗ List (t_var _ (VS VZ : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ List 0ᵛ.
  Proof.
    do 7 constructor.
    econstructor.
    - eapply T_unroll.
      constructor.
      constructor; reflexivity.
    - eapply T_case.
      + constructor.
        apply ListNil_typ.
      + eapply T_bind.
        * eapply T_projL.
          constructor; reflexivity.
        * eapply T_bind.
          -- eapply T_projR.
             constructor; reflexivity.
          -- eapply T_bind.
             ++ eapply T_app.
                ** constructor; reflexivity.
                ** constructor; reflexivity.
             ++ eapply T_bind.
                ** eapply T_app.
                   --- apply ListCons_typ.
                   --- constructor; reflexivity.
                ** eapply T_bind.
                   --- eapply T_app.
                       +++ constructor; reflexivity.
                       +++ constructor; reflexivity.
                   --- eapply T_app.
                       +++ constructor; reflexivity.
                       +++ constructor; reflexivity.
      + constructor; reflexivity.
  Qed.

End ListRec.

Section Vec.

  Definition φvec {Δ} : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp)
    := t_var _ (((VS (VS VZ)) : dom (_ ▹ _ ▹ _ ▹ _))) eq_refl.

  Definition αvec {Δ} : typ KTyp (Δ ▹ (KArr KTyp KTyp) ▹ KTyp ▹ KTyp)
    := t_var _ (VS VZ : dom (_ ▹ _ ▹ _ ▹ _)) eq_refl.

  Definition VecNat {Δ} : typ (KArr KTyp KTyp) Δ
    := rec_type Δ (KArr KTyp KTyp)
         (ƛ (((0ᵛ ≃ Z') ×ᶜ ⊤) + (Nat × (∃ᵗ KTyp , (αvec ≃ S' 0ᵛ) ×ᶜ (φvec 0ᵛ)))))%typ.

  Definition VecNatNonEmpty {Δ} : typ KTyp Δ
    := (∃ᵗ KTyp , VecNat (S' 0ᵛ))%typ.

  Definition VecNatHead {X} : value X
    := (ƛ e_bind (e_unroll (v_var VZ)) (e_case (v_var VZ)
                                          (e_lwith (v_var VZ) e_cabort)
                                          (e_proj L (v_var VZ))))%syn.

  Fact VecNatHead_typed {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ VecNatHead (VecNat (S' τ) →ᵗ Nat)%typ.
  Proof.
    constructor.
    set (body := (ƛ (((0ᵛ ≃ Z') ×ᶜ ⊤) + (Nat × (∃ᵗ KTyp , (αvec ≃ S' 0ᵛ) ×ᶜ (φvec 0ᵛ)))))%typ : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp))).
    set (recBody := subst body VecNat).
    apply T_bind with (recBody (S' τ)).
    - eapply T_unroll.
      apply rel_app_app, rel_app_refl.
      apply T_var; term_simpl; reflexivity.
    - eapply T_case with (((S' τ) ≃ Z') ×ᶜ ⊤)%typ (Nat × (∃ᵗ KTyp , (_ ≃ S' 0ᵛ) ×ᶜ _))%typ.
      + apply T_lwith with (S' τ ≃ Z')%typ ⊤%U.
        * apply T_var; term_simpl; reflexivity.
        * apply T_cabort with (τ + ⊤%U ≃ Z')%typ.
          -- eapply tpi_trans.
             2: apply tpi_ax; constructor; reflexivity.
             eapply tpi_trans.
             2: apply tpi_symm, tpi_beta.
             term_simpl.
             apply Equiv_tproves.
          -- unfold Z'.
             eapply @td_ctd with (KArr KTyp (KArr KTyp KTyp)) KTyp tc_sum tc_void.
             apply inj_app, inj_app, inj_ctor.
             apply inj_ctor.
             unfold cdiscrK.
             destruct (kindEqDec.eq_dec (KArr KTyp (KArr KTyp KTyp)) KTyp) as [H | ?]; [inversion H | constructor].
      + eapply T_projL with (∃ᵗ KTyp, (_ ≃ S' 0ᵛ) ×ᶜ _)%typ.
        apply T_var; term_simpl; reflexivity.
      + eapply T_congV.
        2: apply T_var; term_simpl; reflexivity.
        eapply tpi_trans.
        apply tpi_beta.
        term_simpl.
        apply Equiv_tproves.
  Qed.

  Definition VecNatNonEmptyHead {X} : value X
    := (ƛ e_unpack (v_var VZ) (VecNatHead (v_var VZ)))%syn.

  Fact VecNatNonEmptyHead_typed {X Δ Ψ Γ} : @typing_val X Δ Ψ Γ VecNatNonEmptyHead (VecNatNonEmpty →ᵗ Nat)%typ.
  Proof.
    constructor.
    apply T_unpack with KTyp (VecNat (S' 0ᵛ)).
    apply T_var; term_simpl; reflexivity.
    apply T_app with (VecNat (S' 0ᵛ)).
    - assert (shift Nat = Nat) as ->.
      { term_simpl; reflexivity. }
      apply VecNatHead_typed.
    - apply T_var; term_simpl; reflexivity.
  Qed.

  Definition VecNatNil {X} : value X
    := (v_roll (v_inj L (v_withC v_unit)))%syn.

  Fact VecNatNil_typed {X Δ Ψ Γ} : @typing_val X Δ Ψ Γ VecNatNil (VecNat Z').
  Proof.
    set (body := (ƛ (((0ᵛ ≃ Z') ×ᶜ ⊤) + (Nat × (∃ᵗ KTyp , (αvec ≃ S' 0ᵛ) ×ᶜ (φvec 0ᵛ)))))%typ : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp))).
    set (recBody := subst body VecNat).
    eapply T_roll.
    eapply rel_app_app, rel_app_refl.
    term_simpl.
    eapply T_congV.
    apply tpi_symm, tpi_beta.
    term_simpl.
    constructor.
    apply T_withC.
    constructor.
    apply Equiv_tproves.
  Qed.

  Definition VecNatInj {X} : value X
    := (ƛ v_roll (v_inj R (v_pair (v_var VZ) (v_pack (v_withC VecNatNil)))))%syn.

  Fact VecNatInj_typed {X Δ Ψ Γ} : @typing_val X Δ Ψ Γ VecNatInj (Nat →ᵗ VecNat (S' Z'))%typ.
  Proof.
    set (body := (ƛ (((0ᵛ ≃ Z') ×ᶜ ⊤) + (Nat × (∃ᵗ KTyp , (αvec ≃ S' 0ᵛ) ×ᶜ (φvec 0ᵛ)))))%typ : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp))).
    set (recBody := subst body VecNat).
    do 2 constructor.
    eapply T_roll.
    eapply rel_app_app, rel_app_refl.
    term_simpl.
    eapply T_congV.
    apply tpi_symm, tpi_beta.
    term_simpl.
    do 2 constructor.
    - apply T_var; reflexivity.
    - eapply T_pack.
      term_simpl.
      constructor.
      + apply VecNatNil_typed.
      + apply Equiv_tproves.
  Qed.

  Definition VecNatNonEmptyInj {X} : value X
    := (ƛ e_bind (VecNatInj (v_var VZ)) (v_pack (v_var VZ)) )%syn.

  Fact VecNatNonEmptyInj_typed {X Δ Ψ Γ} : @typing_val X Δ Ψ Γ VecNatNonEmptyInj (Nat →ᵗ VecNatNonEmpty)%typ.
  Proof.
    constructor.
    apply T_bind with (VecNat (S' Z')).
    - apply T_app with Nat.
      apply VecNatInj_typed.
      apply T_var; term_simpl; reflexivity.
    - constructor.
      eapply T_pack.
      term_simpl.
      apply T_var; term_simpl; reflexivity.
  Qed.

  Definition VecNatCons {X} : value X
    := (ƛ ƛ v_roll (v_inj R (v_pair (v_var (VS VZ)) (v_pack (v_withC (v_var VZ))))))%syn.

  Fact VecNatCons_typed {X Δ Ψ Γ τ} : @typing_val X Δ Ψ Γ VecNatCons (Nat →ᵗ VecNat τ →ᵗ VecNat (S' τ))%typ.
  Proof.
    set (body := (ƛ (((0ᵛ ≃ Z') ×ᶜ ⊤) + (Nat × (∃ᵗ KTyp , (αvec ≃ S' 0ᵛ) ×ᶜ (φvec 0ᵛ)))))%typ : typ (KArr KTyp KTyp) (Δ ▹ (KArr KTyp KTyp))).
    set (recBody := subst body VecNat).
    do 4 constructor.
    eapply T_roll.
    eapply rel_app_app, rel_app_refl.
    term_simpl.
    eapply T_congV.
    apply tpi_symm, tpi_beta.
    term_simpl.
    do 2 constructor.
    - apply T_var; reflexivity.
    - eapply T_pack.
      term_simpl.
      constructor.
      + apply T_var; reflexivity.
      + rewrite subst_shift_id.
        apply Equiv_tproves.
  Qed.

  Definition VecNatNonEmptyCons {X} : value X
    := (ƛ ƛ e_unpack (v_var VZ) (e_bind (VecNatCons (v_var (VS (VS VZ))))
                                 (e_bind ((v_var VZ) (v_var (VS VZ)))
                                    (v_pack (v_var VZ)))))%syn.

  Fact VecNatNonEmptyCons_typed {X Δ Ψ Γ} : @typing_val X Δ Ψ Γ VecNatNonEmptyCons (Nat →ᵗ VecNatNonEmpty →ᵗ VecNatNonEmpty)%typ.
  Proof.
    do 3 constructor.
    eapply T_unpack.
    - apply T_var; reflexivity.
    - apply T_bind with (VecNat (S' 0ᵛ) →ᵗ VecNat (S' (S' 0ᵛ)))%typ.
      + apply T_app with Nat.
        * apply VecNatCons_typed.
        * apply T_var; reflexivity.
      + apply T_bind with (VecNat (S' (S' 0ᵛ))).
        * apply T_app with (VecNat (S' 0ᵛ)).
          apply T_var; reflexivity.
          apply T_var; reflexivity.
        * constructor.
          assert (shift VecNatNonEmpty = VecNatNonEmpty) as ->.
          { term_simpl; reflexivity. }
          eapply T_pack.
          term_simpl.
          apply T_var; reflexivity.
  Qed.

  Definition αlistspec {Δ} : typ KTyp (Δ ▹ KTyp ▹ KTyp)
    := t_var ((Δ ▹ _ ▹ _) (VS VZ : dom (Δ ▹ _ ▹ _)))
         (VS VZ : dom (Δ ▹ _ ▹ _))
         eq_refl.

  Definition NonEmptyNatListSpec {Δ} : typ KTyp Δ
    := (∃ᵗ KTyp, (0ᵛ →ᵗ Nat)
                   × ((Nat →ᵗ 0ᵛ)
                        × (Nat →ᵗ 0ᵛ →ᵗ 0ᵛ)))%typ.

  Fact ctx_approx_NonEmptyNatList1 {X Δ Ψ Γ} : (@ctx_approx X Δ Ψ Γ
                                                  (e_val (v_pack (v_pair ListHead (v_pair ListInj ListCons))))%syn
                                                  (e_val (v_pack (v_pair VecNatNonEmptyHead (v_pair VecNatNonEmptyInj VecNatNonEmptyCons))))%syn
                                                  NonEmptyNatListSpec).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iexists (@neu_rel ε (fun u₁ u₂ => (∃ᵢ v₁ v₂ v₃ v₄, (u₁ = v_roll (v_inj R (v_pair v₁ v₂)))ᵢ ∧ᵢ (u₂ = v_pack (v_roll (v_inj R (v_pair v₃ v₄))))ᵢ ∧ᵢ RP (viewG (〚 Nat 〛 η)) v₁ v₃))).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity |].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - iintro u₁; iintro u₂; iintro H.
      eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
      later_shift.
      term_simpl.
      idestruct H as v₁ H;
        idestruct H as v₂ H;
        idestruct H as v₃ H;
        idestruct H as v₄ H;
        idestruct H as H1 H;
        idestruct H as H2 G.
      subst.
      eapply ECL_step'; [constructor; constructor | econstructor 2; [constructor | constructor 1]|].
      later_shift.
      term_simpl.
      eapply ECL_step'; [constructor; constructor | econstructor 2; [constructor | constructor 1]|].
      later_shift.
      term_simpl.
      eapply ECL_step'; [constructor | econstructor 2; [constructor; constructor | constructor 1]|].
      later_shift.
      term_simpl.
      eapply ECL_step; [econstructor 2; constructor|].
      term_simpl.
      eapply ECL_step; [econstructor 2; constructor|].
      term_simpl.
      eapply ECL_step'; [constructor | econstructor 2; [constructor; constructor | constructor 1]|].
      later_shift.
      apply ECL_ret.
      apply (I_fix_unroll _ _ RPR_contr); fold RP.
      apply G.
    - do 4 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |].
      isplit.
      + iintro u₁; iintro u₂; iintro H.
        eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
        later_shift.
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        apply ECL_ret.
        do 4 eapply I_exists_intro;
        isplit; [reflexivity |];
        isplit; [reflexivity |].
        apply (I_fix_roll _ _ RPR_contr) in H; fold RP in H.
        apply H.
      + iintro u₁; iintro u₂; iintro H.
        eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
        later_shift.
        term_simpl.
        apply ECL_ret.
        iintro v₁; iintro v₂; iintro G.
        eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
        later_shift.
        term_simpl.
        idestruct G as w₁ G;
          idestruct G as w₂ G;
          idestruct G as w₃ G;
          idestruct G as w₄ G;
          idestruct G as H1 G;
          idestruct G as H2 G.
        subst.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        apply ECL_ret.
        do 4 eapply I_exists_intro;
        isplit; [reflexivity |];
        isplit; [reflexivity |].
        apply (I_fix_roll _ _ RPR_contr) in H; fold RP in H.
        apply H.
  Qed.

  Fact ctx_approx_NonEmptyNatList2 {X Δ Ψ Γ}
    : (@ctx_approx X Δ Ψ Γ
         (e_val (v_pack (v_pair VecNatNonEmptyHead (v_pair VecNatNonEmptyInj VecNatNonEmptyCons))))%syn
         (e_val (v_pack (v_pair ListHead (v_pair ListInj ListCons))))%syn
         NonEmptyNatListSpec).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iexists (@neu_rel ε (fun u₁ u₂ => (∃ᵢ v₁ v₂ v₃ v₄, (u₂ = v_roll (v_inj R (v_pair v₁ v₂)))ᵢ ∧ᵢ (u₁ = v_pack (v_roll (v_inj R (v_pair v₃ v₄))))ᵢ ∧ᵢ RP (viewG (〚 Nat 〛 η)) v₃ v₁))).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity |].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - iintro u₁; iintro u₂; iintro H.
      eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
      later_shift.
      term_simpl.
      idestruct H as v₁ H;
          idestruct H as v₂ H;
          idestruct H as v₃ H;
          idestruct H as v₄ H;
          idestruct H as H1 H;
          idestruct H as H2 G.
      subst.
      eapply ECL_step';
        [ constructor
        | econstructor 2; [constructor; constructor | constructor 1]|].
      term_simpl.
      later_shift.
      eapply ECL_step';
        [ constructor
        | econstructor 2; [constructor; constructor | constructor 1]|].
      term_simpl.
      later_shift.
      eapply ECL_step';
        [ do 2 constructor
        | econstructor 2; constructor |].
      term_simpl.
      later_shift.
      eapply ECL_step'; [constructor; constructor | econstructor 1 |].
      term_simpl.
      later_shift.
      eapply ECL_step'; [constructor; constructor | econstructor 1 |].
      term_simpl.
      later_shift.
      eapply ECL_step';
        [ do 2 constructor
        | econstructor 2; constructor |].
      later_shift.
      apply ECL_ret.
      apply (I_fix_unroll _ _ RPR_contr); fold RP; simpl.
      apply G.
    - do 4 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |].
      isplit.
      + iintro u₁; iintro u₂; iintro Hu.
        eapply ECL_step';
          [ constructor
          | econstructor 2; [constructor; constructor | constructor 1]|].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ do 2 constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        apply ECL_ret.
        do 4 eapply I_exists_intro;
        isplit; [reflexivity |];
        isplit; [reflexivity |].
        apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
        apply Hu.
      + iintro u₁; iintro u₂; iintro Hu.
        eapply ECL_step';
          [ constructor
          | econstructor 2; [constructor; constructor | constructor 1]|].
        term_simpl.
        later_shift.
        apply ECL_ret.

        iintro v₁; iintro v₂; iintro Hv.
        idestruct Hv as v₁' Hv;
          idestruct Hv as v₂' Hv;
          idestruct Hv as v₃' Hv;
          idestruct Hv as v₄' Hv;
          idestruct Hv as HEQ₁ Hv;
          idestruct Hv as HEQ₂ Hv.
        subst.
        eapply ECL_step';
        [ constructor
        | econstructor 2; constructor |].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ do 2 constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ do 2 constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ do 2 constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        eapply ECL_step';
        [ do 2 constructor
        | econstructor 1 |].
        term_simpl.
        later_shift.
        apply ECL_ret.
        do 4 eapply I_exists_intro;
        isplit; [reflexivity |];
        isplit; [reflexivity |].
        apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
        apply Hu.
  Qed.

  Fact VecCorrect {X Δ Ψ Γ} :
    ∀ {K : pctx X ∅}
      (HK : typing_pctx Δ mtC Ψ nil Γ Env.empty_env K NonEmptyNatListSpec (t_ctor tc_unit)),
    ∀ (v : value ∅),
    (∃ n, nsteps n
            (fill K (e_val (v_pack (v_pair VecNatNonEmptyHead (v_pair VecNatNonEmptyInj VecNatNonEmptyCons))))%syn)
            (e_val v))
    <-> (∃ n, nsteps n
              (fill K (e_val (v_pack (v_pair ListHead (v_pair ListInj ListCons))))%syn)
              (e_val v)).
  Proof.
    intros ? ? ?.
    split; intros ?.
    - eapply ctx_approx_NonEmptyNatList2; eassumption.
    - eapply ctx_approx_NonEmptyNatList1; eassumption.
  Qed.

End Vec.

Section Bool.
  Definition Bool {Δ : Ctx kind} : typ KTyp Δ :=
    (⊤ + ⊤)%typ.

  Definition false {X : Set} : value X :=
    v_inj L v_unit.

  Fact false_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ false : Bool.
  Proof.
    do 2 constructor.
  Qed.

  Definition true {X : Set} : value X :=
    v_inj R v_unit.

  Fact true_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ true : Bool.
  Proof.
    do 2 constructor.
  Qed.

  Definition ifB {X : Set} : value X :=
    (Λ ƛ ƛ ƛ e_case (v_var VZ) (v_var (VS (VS (VZ)))) (v_var (VS (VS (VS (VZ))))))%syn.

  Fact ifB_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ ifB : (∀ᵗ KTyp, 0ᵛ →ᵗ 0ᵛ →ᵗ Bool →ᵗ 0ᵛ)%typ.
  Proof.
    do 7 constructor.
    eapply T_case.
    - do 2 constructor; reflexivity.
    - do 2 constructor; reflexivity.
    - constructor; reflexivity.
  Qed.

  Definition not {X : Set} : value X :=
    (ƛ e_case (v_var VZ) true false)%syn.

  Fact not_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ not : (Bool →ᵗ Bool)%typ.
  Proof.
    constructor.
    eapply T_case.
    - constructor; apply true_typ.
    - constructor; apply false_typ.
    - constructor; reflexivity.
  Qed.

  Definition NotSpec {Δ : Ctx kind} : typ KTyp Δ :=
    (∃ᵗ KTyp , 0ᵛ × (0ᵛ →ᵗ Bool))%typ.

  Definition is_zero {X : Set} : value X :=
    (ƛ ((e_unroll (v_var VZ)) >>= e_case (v_var VZ) true false))%syn.

  Fact is_zero_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ is_zero : (Nat →ᵗ ⊤ + ⊤).
  Proof.
    constructor.
    econstructor.
    - eapply T_unroll; [| constructor; reflexivity].
      constructor.
    - term_simpl.
      eapply T_case.
      + constructor; apply true_typ.
      + constructor; apply false_typ.
      + constructor; reflexivity.
  Qed.

  Definition impl1 {X : Set} : value X :=
    v_pack (v_pair (S Z) is_zero).

  Fact impl1_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ impl1 : NotSpec.
  Proof.
    eapply T_pack.
    term_simpl.
    constructor.
    - apply S_typ, Z_typ.
    - apply is_zero_typ.
  Qed.

  Definition impl2 {X : Set} : value X :=
    v_pack (v_pair true not).

  Fact impl2_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ impl2 : NotSpec.
  Proof.
    eapply T_pack.
    term_simpl.
    constructor.
    - apply true_typ.
    - apply not_typ.
  Qed.

  Fact ctx_approx_not1 {X Δ Ψ Γ}
    : (@ctx_approx X Δ Ψ Γ
         (e_val impl1)%syn
         (e_val impl2)%syn
         NotSpec).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iexists (@neu_rel ε (fun u₁ u₂ => (u₁ = S Z ∧ u₂ = true)ᵢ)).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity |].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - split; reflexivity.
    - iintro u₁; iintro u₂; iintro H.
      destruct H as [-> ->].
      eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
      later_shift.
      term_simpl.
      eapply ECL_step; [econstructor 2; constructor; constructor |].
      term_simpl.
      eapply ECL_step'; [constructor; constructor | constructor 1 |].
      later_shift.
      eapply ECL_step'; [constructor; constructor | constructor 1 |].
      later_shift.
      term_simpl.
      eapply ECL_step'; [constructor; constructor | constructor 1 |].
      later_shift.
      term_simpl.
      apply ECL_ret.
      ileft.
      do 2 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |];
      isplit; reflexivity.
  Qed.

  Fact ctx_approx_not2 {X Δ Ψ Γ}
    : (@ctx_approx X Δ Ψ Γ
         (e_val impl2)%syn
         (e_val impl1)%syn
         NotSpec).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iexists (@neu_rel ε (fun u₁ u₂ => (u₂ = S Z ∧ u₁ = true)ᵢ)).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity |].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - split; reflexivity.
    - iintro u₁; iintro u₂; iintro H.
      destruct H as [-> ->].
      eapply ECL_step'; [constructor | econstructor 2; [constructor | constructor 1]|].
      later_shift.
      term_simpl.
      eapply ECL_step; [econstructor 2; constructor; constructor |].
      eapply ECL_step'; [constructor; constructor | constructor 1 |].
      later_shift.
      term_simpl.
      eapply ECL_step; [econstructor 2; constructor; constructor |].
      term_simpl.
      eapply ECL_step; [econstructor 2; constructor; constructor |].
      term_simpl.
      apply ECL_ret.
      ileft.
      do 2 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |];
      isplit; reflexivity.
  Qed.

  Fact NotCorrect {X Δ Ψ Γ} :
    ∀ {K : pctx X ∅}
      (HK : typing_pctx Δ mtC Ψ nil Γ Env.empty_env K NotSpec (t_ctor tc_unit)),
    ∀ (v : value ∅),
    (∃ n, nsteps n
            (fill K (e_val impl1)%syn)
            (e_val v))
    <-> (∃ n, nsteps n
              (fill K (e_val impl2)%syn)
              (e_val v)).
  Proof.
    intros ? ? ?.
    split; intros ?.
    - eapply ctx_approx_not1; eassumption.
    - eapply ctx_approx_not2; eassumption.
  Qed.

  Definition BoolPoly {Δ : Ctx kind} : typ KTyp Δ
    := (∀ᵗ KTyp, 0ᵛ →ᵗ 0ᵛ →ᵗ 0ᵛ)%typ.

  Definition truePoly {X : Set} : value X
    := (Λ ƛ ƛ (v_var (VS VZ)))%syn.

  Fact truePoly_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ truePoly : BoolPoly.
  Proof.
    do 7 constructor; reflexivity.
  Qed.

  Definition falsePoly {X : Set} : value X
    := (Λ ƛ ƛ (v_var VZ))%syn.

  Fact falsePoly_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ falsePoly : BoolPoly.
  Proof.
    do 7 constructor; reflexivity.
  Qed.

  Definition ifBPoly {X : Set} : value X
    := (Λ ƛ ƛ ƛ e_tapp (v_var VZ) >>= (v_var VZ) (v_var (VS (VS (VS VZ)))) >>= (v_var VZ) (v_var (VS (VS (VS VZ)))))%syn.

  Fact ifBPoly_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ}
    : Δ ∣ Ψ ∣ Γ ⊢ᵥ ifBPoly : (∀ᵗ KTyp, 0ᵛ →ᵗ 0ᵛ →ᵗ BoolPoly →ᵗ 0ᵛ)%typ.
  Proof.
    do 7 constructor.
    eapply T_bind.
    - do 2 constructor; reflexivity.
    - eapply T_bind.
      + term_simpl.
        eapply T_app.
        * constructor; reflexivity.
        * constructor; reflexivity.
      + eapply T_app.
        * constructor; reflexivity.
        * constructor; reflexivity.
  Qed.

  Definition BoolSpec {Δ : Ctx kind} : typ KTyp Δ
    := (∃ᵗ KTyp , 0ᵛ × (0ᵛ × (∀ᵗ KTyp, 0ᵛ →ᵗ 0ᵛ →ᵗ (t_var _ (VS VZ : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ 0ᵛ)))%typ.

  Fact ctx_approx_bool1 {X Δ Ψ Γ}
    : (@ctx_approx X Δ Ψ Γ
         (e_val (v_pack (v_pair true (v_pair false ifB))))%syn
         (e_val (v_pack (v_pair truePoly (v_pair falsePoly ifBPoly))))%syn
         BoolSpec).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iexists (@neu_rel ε (fun u₁ u₂ => ((u₁ = v_inj L v_unit ∧ u₂ = (Λ ƛ ƛ v_var VZ)%syn) ∨ (u₁ = v_inj R v_unit ∧ u₂ = (Λ ƛ ƛ v_var (VS VZ))%syn))ᵢ)).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity | term_simpl].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - right; split; reflexivity.
    - do 4 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |];
      isplit; [left; split; reflexivity |].
      do 2 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |].
      iintro μ; iintro Hμ.
      later_shift.
      apply ECL_ret.
      term_simpl.
      rewrite !map_id'.
      apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
      iintro u₁; iintro u₂; iintro Hu.
      eapply ECL_step'; [do 2 constructor | econstructor 2; constructor |].
      later_shift; term_simpl.
      apply ECL_ret.
      iintro u₁'; iintro u₂'; iintro Hu'.
      eapply ECL_step'; [do 2 constructor | econstructor 2; constructor |].
      later_shift; term_simpl.
      apply ECL_ret.
      iintro u₁''; iintro u₂''; iintro Hu''.
      eapply ECL_step'; [do 2 constructor | econstructor 2; constructor |].
      later_shift; term_simpl.
      destruct Hu'' as [[Hu'' Hu'''] | [Hu'' Hu''']]; rewrite Hu'', Hu'''.
      + eapply ECL_step'; [do 2 constructor | econstructor 2; do 2 constructor |].
        later_shift; term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        apply ECL_ret.
        apply Hu'.
      + eapply ECL_step'; [do 2 constructor | econstructor 2; do 2 constructor |].
        later_shift; term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        eapply ECL_step; [econstructor 2; constructor; constructor |].
        term_simpl.
        apply ECL_ret.
        apply Hu.
  Qed.

  Fact ctx_approx_bool2 {X Δ Ψ Γ}
    : (@ctx_approx X Δ Ψ Γ
         (e_val (v_pack (v_pair truePoly (v_pair falsePoly ifBPoly))))%syn
         (e_val (v_pack (v_pair true (v_pair false ifB))))%syn
         BoolSpec).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iexists (@neu_rel ε (fun u₂ u₁ => ((u₁ = v_inj L v_unit ∧ u₂ = (Λ ƛ ƛ v_var VZ)%syn) ∨ (u₁ = v_inj R v_unit ∧ u₂ = (Λ ƛ ƛ v_var (VS VZ))%syn))ᵢ)).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity | term_simpl].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - right; split; reflexivity.
    - do 4 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |];
      isplit; [left; split; reflexivity |].
      do 2 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |].
      iintro μ; iintro Hμ.
      later_shift.
      apply ECL_ret.
      term_simpl.
      rewrite !map_id'.
      apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
      iintro u₁; iintro u₂; iintro Hu.
      eapply ECL_step'; [do 2 constructor | econstructor 2; constructor |].
      later_shift; term_simpl.
      apply ECL_ret.
      iintro u₁'; iintro u₂'; iintro Hu'.
      eapply ECL_step'; [do 2 constructor | econstructor 2; constructor |].
      later_shift; term_simpl.
      apply ECL_ret.
      iintro u₁''; iintro u₂''; iintro Hu''.
      eapply ECL_step'; [do 2 constructor | econstructor 2; constructor |].
      later_shift; term_simpl.
      destruct Hu'' as [[Hu'' Hu'''] | [Hu'' Hu''']]; rewrite Hu'', Hu'''.
      + eapply ECL_step'; [do 2 constructor | econstructor 2; do 2 constructor |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        apply ECL_ret.
        apply Hu'.
      + eapply ECL_step'; [do 2 constructor | econstructor 2; do 2 constructor |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        eapply ECL_step'; [do 2 constructor | constructor 1 |].
        later_shift; term_simpl.
        apply ECL_ret.
        apply Hu.
  Qed.

  Fact BoolCorrect {X Δ Ψ Γ} :
    ∀ {K : pctx X ∅}
      (HK : typing_pctx Δ mtC Ψ nil Γ Env.empty_env K BoolSpec (t_ctor tc_unit)),
    ∀ (v : value ∅),
    (∃ n, nsteps n
            (fill K (e_val (v_pack (v_pair true (v_pair false ifB))))%syn)
            (e_val v))
    <-> (∃ n, nsteps n
              (fill K (e_val (v_pack (v_pair truePoly (v_pair falsePoly ifBPoly))))%syn)
              (e_val v)).
  Proof.
    intros ? ? ?.
    split; intros ?.
    - eapply ctx_approx_bool1; eassumption.
    - eapply ctx_approx_bool2; eassumption.
  Qed.

End Bool.

Section ListPoly.

  Definition ListPoly {Δ : Ctx kind} (τ : typ KTyp Δ) : typ KTyp Δ
    := (∀ᵗ KTyp, 0ᵛ →ᵗ ((shift τ) →ᵗ 0ᵛ →ᵗ 0ᵛ) →ᵗ 0ᵛ)%typ.

  Definition NilPoly {X : Set} : value X
    := (Λ ƛ ƛ (v_var (VS VZ)))%syn.

  Fact NilPoly_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} (τ : typ KTyp Δ)
    : Δ ∣ Ψ ∣ Γ ⊢ᵥ NilPoly : ListPoly τ.
  Proof.
    do 7 constructor; reflexivity.
  Qed.

  Definition ConsPoly {X : Set} : value X
    := (ƛ ƛ Λ ƛ ƛ bind_app
          (bind_app (v_var VZ) (v_var (VS (VS (VS VZ)))))
          (bind_app (bind_app (e_tapp (v_var (VS (VS VZ)))) (v_var (VS VZ))) (v_var VZ)))%syn.

  Fact ConsPoly_typ {X : Set} {Δ Ψ} {Γ : X → typ KTyp Δ} (τ : typ KTyp Δ)
    : Δ ∣ Ψ ∣ Γ ⊢ᵥ ConsPoly : τ →ᵗ ListPoly τ →ᵗ ListPoly τ.
  Proof.
    do 9 constructor.
    apply @bind_app_typ with (0ᵛ)%typ.
    - apply @bind_app_typ with (shift τ).
      + do 2 constructor; reflexivity.
      + do 2 constructor; reflexivity.
    - apply @bind_app_typ with ((shift τ) →ᵗ 0ᵛ →ᵗ 0ᵛ)%typ.
      + apply @bind_app_typ with (0ᵛ)%typ.
        * match goal with
          | |- context G [_ ∣ _ ∣ _ ⊢ₑ _ : ?a] =>
              assert (a = subst (0ᵛ →ᵗ ((shift (shift τ)) →ᵗ 0ᵛ →ᵗ 0ᵛ) →ᵗ 0ᵛ : typ KTyp (Δ ▹ KTyp ▹ KTyp))%typ (0ᵛ : typ KTyp (Δ ▹ KTyp))%typ) as ->
          end.
          { term_simpl; reflexivity. }
          do 2 constructor; term_simpl; reflexivity.
        * do 2 constructor; reflexivity.
      + do 2 constructor; reflexivity.
  Qed.

  Definition HeadPoly' {X : Set} : value X
    := (ƛ bind_app (bind_app (e_tapp (v_var VZ)) (ƛ loop)) (ƛ ƛ ƛ (v_var (VS (VS VZ)))))%syn.

  Fact HeadPoly'_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} (τ : typ KTyp Δ) : Δ ∣ Ψ ∣ Γ ⊢ᵥ HeadPoly' : (ListPoly τ →ᵗ ⊤ →ᵗ τ)%typ.
  Proof.
    constructor.
    eapply bind_app_typ.
    - eapply bind_app_typ.
      + match goal with
        | |- context G [_ ∣ _ ∣ _ ⊢ₑ _ : ?a] =>
            assert (a = subst (0ᵛ →ᵗ ((shift τ) →ᵗ 0ᵛ →ᵗ 0ᵛ) →ᵗ 0ᵛ : typ KTyp (Δ ▹ KTyp))%typ (⊤%U →ᵗ τ : typ KTyp Δ)%typ) as ->
        end.
        { term_simpl; reflexivity. }
        do 2 constructor; term_simpl; reflexivity.
      + do 2 constructor; apply loop_typ.
    - do 8 constructor; reflexivity.
  Qed.

  Definition HeadPoly {X : Set} : value X
    := (ƛ bind_app (HeadPoly' (v_var VZ)) v_unit)%syn.

  Fact HeadPoly_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} (τ : typ KTyp Δ) : Δ ∣ Ψ ∣ Γ ⊢ᵥ HeadPoly : (ListPoly τ →ᵗ τ)%typ.
  Proof.
    constructor.
    eapply bind_app_typ.
    - eapply T_app.
      + apply HeadPoly'_typ.
      + constructor; reflexivity.
    - do 2 constructor.
  Qed.

  Definition MapPoly {X : Set} : value X
    := (ƛ ƛ Λ ƛ ƛ bind_app
          (bind_app (e_tapp (v_var (VS (VS VZ)))) (v_var (VS VZ)))
          (ƛ ƛ bind_app (bind_app (v_var (VS (VS VZ))) ((v_var (VS (VS (VS (VS (VS VZ)))))) (v_var (VS VZ)))) (v_var VZ)))%syn.

  Fact MapPoly_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} (τ σ : typ KTyp Δ) : Δ ∣ Ψ ∣ Γ ⊢ᵥ MapPoly : ((τ →ᵗ σ) →ᵗ ListPoly τ →ᵗ ListPoly σ)%typ.
  Proof.
    do 9 constructor.
    eapply bind_app_typ.
    - eapply bind_app_typ.
      + match goal with
        | |- context G [_ ∣ _ ∣ _ ⊢ₑ _ : ?a] =>
            assert (a = subst ((0ᵛ →ᵗ (shift (shift τ) →ᵗ 0ᵛ →ᵗ 0ᵛ) →ᵗ 0ᵛ) : typ KTyp (Δ ▹ KTyp ▹ KTyp))%typ (0ᵛ : typ KTyp (Δ ▹ KTyp))%typ) as H
        end.
        * term_simpl; reflexivity.
        * rewrite H.
          apply T_tapp.
          constructor; term_simpl.
          reflexivity.
      + do 2 constructor; term_simpl; reflexivity.
    - do 4 constructor.
      eapply bind_app_typ.
      + eapply bind_app_typ.
        * do 2 constructor; term_simpl; reflexivity.
        * eapply T_app.
          -- constructor; term_simpl; reflexivity.
          -- constructor; term_simpl; reflexivity.
      + do 2 constructor; term_simpl; reflexivity.
  Qed.

  Definition HeadPolyPoly {X : Set} : value X
    := (Λ HeadPoly)%syn.

  Fact HeadPolyPoly_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ HeadPolyPoly : (∀ᵗ KTyp, ListPoly 0ᵛ →ᵗ 0ᵛ)%typ.
  Proof.
    do 2 constructor.
    apply HeadPoly_typ.
  Qed.

  Definition MapPolyPoly {X : Set} : value X
    := (Λ Λ MapPoly)%syn.

  Fact MapPolyPoly_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ MapPolyPoly : (∀ᵗ KTyp, ∀ᵗ KTyp, ((t_var _ (VS VZ : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ 0ᵛ) →ᵗ ListPoly (t_var _ (VS VZ : dom (_ ▹ _ ▹ _)) eq_refl) →ᵗ ListPoly 0ᵛ)%typ.
  Proof.
    do 4 constructor.
    apply MapPoly_typ.
  Qed.

End ListPoly.

Section Sign.

  (* (pos, z) + neg *)
  Definition Sign {Δ : Ctx kind} : typ KTyp Δ
    := (Nat + Nat)%typ.

  Definition szero {X : Set} : value X
    := v_inj L Z.

  Fact szero_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ szero : Sign.
  Proof.
    constructor.
    apply Z_typ.
  Qed.

  Definition iszero_elim {X : Set} : value X
    := (ƛ ƛ ƛ e_unroll (v_var (VS (VS VZ)))
          >>= e_case (v_var VZ) (v_var (VS (VS (VS VZ)))) ((v_var (VS (VS VZ))) (v_var VZ)))%syn.

  Fact iszero_elim_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} {τ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ iszero_elim : (Nat →ᵗ τ →ᵗ (Nat →ᵗ τ) →ᵗ τ)%typ.
  Proof.
    do 5 constructor.
    eapply T_bind.
    - eapply T_unroll.
      constructor.
      constructor; reflexivity.
    - eapply T_case.
      + do 2 constructor; reflexivity.
      + eapply T_app.
        * constructor; reflexivity.
        * constructor; reflexivity.
      + constructor; reflexivity.
  Qed.

  Definition dec {X : Set} : value X
    := (ƛ e_unroll (v_var VZ)
          >>= e_case (v_var VZ) Z (v_var VZ))%syn.

  Fact dec_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ dec : (Nat →ᵗ Nat)%typ.
  Proof.
    constructor.
    eapply T_bind.
    - eapply T_unroll.
      + constructor.
      + constructor; reflexivity.
    - term_simpl.
      eapply T_case.
      + constructor; apply Z_typ.
      + do 2 constructor; reflexivity.
      + constructor; reflexivity.
  Qed.

  Definition sinc {X : Set} : value X
    := (ƛ e_case (v_var VZ)
          (v_inj L (S (v_var VZ)))
          (iszero_elim (v_var VZ)
             >>= (v_var VZ) (v_inj L (S Z))
             >>= (v_var VZ) (ƛ (iszero_elim (v_var VZ)
                                  >>= (v_var VZ) (v_inj L Z)
                                  >>= (v_inj R (v_var (VS (VS VZ))))))))%syn.

  Fact sinc_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ sinc : (Sign →ᵗ Sign)%typ.
  Proof.
    constructor.
    eapply T_case with (τ := Sign).
    - do 2 constructor; apply S_typ.
      constructor; reflexivity.
    - eapply T_bind.
      + eapply T_app.
        * apply (@iszero_elim_typ _ _ _ _ Sign).
        * constructor; reflexivity.
      + eapply T_bind.
        * eapply T_app.
          -- constructor; reflexivity.
          -- econstructor; apply S_typ, Z_typ.
        * eapply T_app.
          -- constructor; reflexivity.
          -- constructor.
             eapply T_bind.
             ++ eapply T_app.
                ** apply (@iszero_elim_typ _ _ _ _ Sign).
                ** constructor; reflexivity.
             ++ eapply T_bind.
                ** eapply T_app.
                   --- constructor; reflexivity.
                   --- apply T_injl, Z_typ.
                ** constructor; apply T_injr; constructor; reflexivity.
    - constructor; reflexivity.
  Qed.

  Definition iszero {X : Set} : value X
    := (ƛ e_unroll (v_var VZ)
          >>= e_case (v_var VZ) true false)%syn.

  Fact iszero_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ iszero : (Nat →ᵗ Bool)%typ.
  Proof.
    constructor.
    eapply T_bind.
    eapply T_unroll.
    constructor.
    constructor; reflexivity.
    eapply T_case.
    - constructor; apply true_typ.
    - constructor; apply false_typ.
    - constructor; reflexivity.
  Qed.

  Definition siszero {X : Set} : value X
    := (ƛ e_case (v_var VZ) (iszero (v_var VZ)) (iszero (v_var VZ)))%syn.

  Fact siszero_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ siszero : (Sign →ᵗ Bool)%typ.
  Proof.
    constructor.
    eapply T_case.
    - eapply T_app.
      apply iszero_typ.
      constructor; reflexivity.
    - eapply T_app.
      apply iszero_typ.
      constructor; reflexivity.
    - constructor; reflexivity.
  Qed.

  Definition sdec {X : Set} : value X
    := (ƛ e_case (v_var VZ)
          (iszero_elim (v_var VZ)
             >>= (v_var VZ) (v_inj R (S Z))
             >>= (v_var VZ) (ƛ (v_inj L (v_var VZ))))
          (v_inj R (S (v_var VZ))))%syn.

  Fact sdec_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ sdec : (Sign →ᵗ Sign)%typ.
  Proof.
    constructor.
    eapply T_case.
    - eapply T_bind.
      + eapply T_app.
        * apply (@iszero_elim_typ _ _ _ _ Sign).
        * constructor; reflexivity.
      + eapply T_bind.
        * eapply T_app.
          -- constructor; reflexivity.
          -- econstructor; apply S_typ, Z_typ.
        * eapply T_app.
          -- constructor; reflexivity.
          -- do 2 constructor.
             apply T_injl.
             constructor; reflexivity.
    - do 2 constructor; apply S_typ.
      constructor; reflexivity.
    - constructor; reflexivity.
  Qed.

End Sign.

Section Diff.
  (* pos × neg *)
  Definition Diff {Δ : Ctx kind} : typ KTyp Δ
    := (Nat × Nat)%typ.

  Definition dzero {X : Set} : value X
    := v_pair Z Z.

  Fact dzero_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ dzero : Diff.
  Proof.
    constructor; apply Z_typ.
  Qed.

  Definition andB {X : Set} : value X
    := (ƛ ƛ e_case (v_var VZ) false (e_case (v_var (VS (VS VZ))) false true))%syn.

  Fact andB_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ andB : (Bool →ᵗ Bool →ᵗ Bool)%typ.
  Proof.
    do 3 constructor.
    eapply T_case.
    - constructor; apply false_typ.
    - eapply T_case.
      + constructor; apply false_typ.
      + constructor; apply true_typ.
      + constructor; reflexivity.
    - constructor; reflexivity.
  Qed.

  Definition diszero {X : Set} : value X
    := (ƛ bind_app
          (bind_app andB (bind_app iszero (e_proj L (v_var VZ))))
          (bind_app iszero (e_proj R (v_var VZ))))%syn.

  Fact diszero_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ diszero : (Diff →ᵗ Bool)%typ.
  Proof.
    constructor.
    eapply bind_app_typ.
    - eapply bind_app_typ.
      + constructor; apply andB_typ.
      + eapply bind_app_typ.
        * constructor; apply iszero_typ.
        * eapply T_projL.
          constructor; reflexivity.
    - eapply bind_app_typ.
      + constructor; apply iszero_typ.
      + eapply T_projR.
        constructor; reflexivity.
  Qed.

  Definition ddec {X : Set} : value X
    := (ƛ e_proj L (v_var VZ)
          >>= e_proj R (v_var (VS VZ))
          >>= iszero_elim (v_var (VS VZ))
          >>= (v_var VZ) (v_pair Z (S (v_var (VS VZ))))
          >>= (v_var VZ) (ƛ v_pair (v_var VZ) (v_var (VS (VS (VS VZ))))))%syn.

  Fact ddec_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ ddec : (Diff →ᵗ Diff)%typ.
  Proof.
    constructor.
    eapply T_bind.
    - eapply T_projL.
      constructor; reflexivity.
    - eapply T_bind.
      + eapply T_projR.
        constructor; reflexivity.
      + eapply T_bind.
        * eapply T_app.
          -- eapply iszero_elim_typ.
          -- constructor; reflexivity.
        * eapply T_bind.
          -- eapply T_app.
             ++ constructor; reflexivity.
             ++ constructor.
                apply Z_typ.
                apply S_typ.
                constructor; reflexivity.
          -- eapply T_app.
             ++ constructor; reflexivity.
             ++ do 3 constructor.
                constructor; reflexivity.
                constructor; reflexivity.
  Qed.

  Definition dinc {X : Set} : value X
    := (ƛ e_proj L (v_var VZ)
          >>= e_proj R (v_var (VS VZ))
          >>= iszero_elim (v_var VZ)
          >>= (v_var VZ) (v_pair (S (v_var (VS (VS VZ)))) Z) >>=
          (v_var VZ) (ƛ v_pair (v_var (VS (VS (VS (VS VZ))))) (v_var VZ)))%syn.

  Fact dinc_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ dinc : (Diff →ᵗ Diff)%typ.
  Proof.
    constructor.
    eapply T_bind.
    - eapply T_projL.
      constructor; reflexivity.
    - eapply T_bind.
      + eapply T_projR.
        constructor; reflexivity.
      + eapply T_bind.
        * eapply T_app.
          -- eapply iszero_elim_typ.
          -- constructor; reflexivity.
        * eapply T_bind.
          -- eapply T_app.
             ++ constructor; reflexivity.
             ++ constructor.
                apply S_typ.
                constructor; reflexivity.
                apply Z_typ.
          -- eapply T_app.
             ++ constructor; reflexivity.
             ++ do 3 constructor.
                constructor; reflexivity.
                constructor; reflexivity.
  Qed.

End Diff.

Section Counter.

  Definition IncCounter {Δ : Ctx kind} : typ KTyp Δ
    := (∃ᵗ KTyp , 0ᵛ × ((0ᵛ →ᵗ 0ᵛ) × ((0ᵛ →ᵗ 0ᵛ) × (0ᵛ →ᵗ Bool))))%typ.

  Definition IncCounter1 {X : Set} : value X :=
    v_pack (v_pair szero (v_pair sdec (v_pair sinc siszero))).

  Definition IncCounter2 {X : Set} : value X :=
    v_pack (v_pair dzero (v_pair ddec (v_pair dinc diszero))).

  Fact ctx_approx_counter1 {X Δ Ψ Γ}
    : (@ctx_approx X Δ Ψ Γ
         (e_val IncCounter1)%syn
         (e_val IncCounter2)%syn
         IncCounter).
  Proof.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    unfold IncCounter1.
    Opaque szero sdec sinc siszero.
    unfold IncCounter2.
    Opaque dzero ddec dinc diszero.
    Opaque dec.
    Opaque iszero.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    (* pos + neg *)
    (* pos × neg *)
    iexists (@neu_rel ε (fun u₁ u₂ => ((∃ᵢ n m, (u₁ = v_inj R n ∧ u₂ = v_pair Z m)ᵢ
                                               ∧ᵢ RP (viewG (〚 Nat 〛 η)) n m)
                                      ∨ᵢ (∃ᵢ n m, (u₁ = v_inj L n ∧ u₂ = v_pair m Z)ᵢ
                                                    ∧ᵢ RP (viewG (〚 Nat 〛 η)) n m)))).
    isplit; [unfold interpNeu; simpl; foldArrs; reflexivity |].
    apply I_later_intro.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    do 4 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    isplit.
    - iright.
      do 2 eapply I_exists_intro.
      isplit.
      split; reflexivity.
      term_simpl.
      pose proof (@Z_typ X Δ Ψ Γ) as HT.
      apply fl_val in HT.
      specialize (HT η Hη HΨ γ γ' n Hγ).
      apply HT.
    - do 4 eapply I_exists_intro;
      isplit; [reflexivity |];
      isplit; [reflexivity |].
      isplit.
      + iintro u₁; iintro u₂; iintro H.
        idestruct H as H H.
        * idestruct H as p H;
            idestruct H as m H;
            idestruct H as HH H.
          destruct HH as [-> ->].
          do 2 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
          do 11 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
          apply ECL_ret.
          ileft.
          do 2 eapply I_exists_intro;
          isplit; [split; reflexivity |].
          apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
          unfold viewG; simpl.
          destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
          rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
          clear EQ₁ EQ₂.
          do 2 eapply I_exists_intro;
          isplit; [reflexivity |];
          isplit; [reflexivity |].
          later_shift.
          genEQ HH.
          simpl.
          intros HH.
          rewrite UIP_refl with (p := HH); simpl.
          term_simpl.
          apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
          iright.
          do 2 eapply I_exists_intro;
          isplit; [reflexivity |];
          isplit; [reflexivity |].
          apply (I_fix_unroll _ _ RPR_contr); fold RP; simpl.
          apply H.
        * idestruct H as p H;
            idestruct H as m H;
            idestruct H as HH H.
          destruct HH as [-> ->].
          do 7 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
          do 3 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
          match goal with
          | |- context G [_ ⊨ ECL ?a _ _] => set (T := a)
          end.
          iapply (@ECL_bind n (RP (viewG (〚 (⊤ + Nat)%typ 〛 η))) T).
          -- apply (I_fix_unroll _ _ RPR_contr) in H; simpl in H.
             unfold viewG in H; simpl in H.
             destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
             rewrite UIP_refl with (p := EQ₂) in H; simpl in H; rewrite !UIP_refl with (p := EQ₁) in H.
             clear EQ₁ EQ₂.
             idestruct H as va H;
               idestruct H as vb H;
               idestruct H as Hva H;
               idestruct H as Hvb H.
             rewrite Hva, Hvb.
             do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             term_simpl in H.
             apply ECL_ret.
             fold RP in H.
             revert H.
             genEQ HH.
             simpl.
             intros HH.
             rewrite UIP_refl with (p := HH); simpl.
             intros H.
             apply H.
          -- iintro v₁; iintro v₂; iintro Hv.
             do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             subst T.
             apply (I_fix_unroll _ _ RPR_contr) in Hv; simpl in Hv.
             idestruct Hv as Hv Hv.
             ++ idestruct Hv as va Hv;
                  idestruct Hv as vb Hv;
                  idestruct Hv as Hva Hv;
                  idestruct Hv as Hvb Hv.
                rewrite Hva, Hvb.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                apply ECL_ret.
                ileft.
                do 2 eapply I_exists_intro.
                isplit.
                split; [reflexivity | reflexivity].
                apply (I_fix_roll _ _ RPR_contr); simpl.
                unfold viewG; simpl.
                destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
                rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
                clear EQ₁ EQ₂.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [split; reflexivity |].
                later_shift.
                apply (I_fix_roll _ _ RPR_contr); simpl.
                unfold viewG; simpl.
                genEQ HH.
                simpl; intros HH.
                rewrite UIP_refl with (p := HH); simpl.
                clear HH.
                iright.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [split; reflexivity |].
                destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
                rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
                clear EQ₁ EQ₂.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [split; reflexivity |].
                later_shift.
                apply (I_fix_roll _ _ RPR_contr); simpl.
                unfold viewG; simpl.
                genEQ HH.
                simpl; intros HH.
                rewrite UIP_refl with (p := HH); simpl.
                clear HH.
                ileft.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [split; reflexivity |].
                isplit; reflexivity.
             ++ idestruct Hv as va Hv;
                  idestruct Hv as vb Hv;
                  idestruct Hv as Hva Hv;
                  idestruct Hv as Hvb Hv.
                rewrite Hva, Hvb.
                do 2 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                apply ECL_ret.
                iright.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
                apply Hv.
      + do 4 eapply I_exists_intro;
        isplit; [reflexivity |];
        isplit; [reflexivity |].
        isplit.
        * iintro u₁; iintro u₂; iintro H.
          idestruct H as H H.
          -- idestruct H as p H;
               idestruct H as m H;
               idestruct H as HH H.
             destruct HH as [-> ->].
             do 7 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             do 3 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
             match goal with
             | |- context G [_ ⊨ ECL ?a _ _] => set (T := a)
             end.
             iapply (@ECL_bind n (RP (viewG (〚 (⊤ + Nat)%typ 〛 η_id))) T).
             ++ apply (I_fix_unroll _ _ RPR_contr) in H; simpl in H.
                unfold viewG in H; simpl in H.
                destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
                rewrite UIP_refl with (p := EQ₂) in H; simpl in H; rewrite !UIP_refl with (p := EQ₁) in H.
                clear EQ₁ EQ₂.
                idestruct H as va H;
                  idestruct H as vb H;
                  idestruct H as Hva H;
                  idestruct H as Hvb H.
                rewrite Hva, Hvb.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                term_simpl in H.
                apply ECL_ret.
                fold RP in H.
                revert H.
                genEQ HH.
                simpl.
                intros HH.
                rewrite UIP_refl with (p := HH); simpl.
                intros H.
                apply H.
             ++ iintro v₁; iintro v₂; iintro Hv.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                subst T.
                apply (I_fix_unroll _ _ RPR_contr) in Hv; simpl in Hv.
                idestruct Hv as Hv Hv.
                ** idestruct Hv as va Hv;
                     idestruct Hv as vb Hv;
                     idestruct Hv as Hva Hv;
                     idestruct Hv as Hvb Hv.
                   rewrite Hva, Hvb.
                   do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                   apply ECL_ret.
                   iright.
                   do 2 eapply I_exists_intro.
                   isplit.
                   split; [reflexivity | reflexivity].
                   apply (I_fix_roll _ _ RPR_contr); simpl.
                   unfold viewG; simpl.
                   destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
                   rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
                   clear EQ₁ EQ₂.
                   do 2 eapply I_exists_intro;
                   isplit; [split; reflexivity |].
                   isplit; [split; reflexivity |].
                   later_shift.
                   apply (I_fix_roll _ _ RPR_contr); simpl.
                   unfold viewG; simpl.
                   genEQ HH.
                   simpl; intros HH.
                   rewrite UIP_refl with (p := HH); simpl.
                   clear HH.
                   iright.
                   do 2 eapply I_exists_intro;
                   isplit; [split; reflexivity |].
                   isplit; [split; reflexivity |].
                   destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
                   rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
                   clear EQ₁ EQ₂.
                   do 2 eapply I_exists_intro;
                   isplit; [split; reflexivity |].
                   isplit; [split; reflexivity |].
                   later_shift.
                   apply (I_fix_roll _ _ RPR_contr); simpl.
                   unfold viewG; simpl.
                   genEQ HH.
                   simpl; intros HH.
                   rewrite UIP_refl with (p := HH); simpl.
                   clear HH.
                   ileft.
                   do 2 eapply I_exists_intro;
                   isplit; [split; reflexivity |].
                   isplit; [split; reflexivity |].
                   isplit; reflexivity.
                ** idestruct Hv as va Hv;
                     idestruct Hv as vb Hv;
                     idestruct Hv as Hva Hv;
                     idestruct Hv as Hvb Hv.
                   rewrite Hva, Hvb.
                   do 2 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                   do 4 (eapply ECL_step'; [repeat constructor | constructor 1 | term_simpl; later_shift]).
                   apply ECL_ret.
                   ileft.
                   do 2 eapply I_exists_intro;
                   isplit; [split; reflexivity |].
                   apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
                   apply Hv.
          -- idestruct H as p H;
               idestruct H as m H;
               idestruct H as HH H.
             destruct HH as [-> ->].
             do 2 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             do 11 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
             apply ECL_ret.
             iright.
             do 2 eapply I_exists_intro;
             isplit; [split; reflexivity |].
             apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
             unfold viewG; simpl.
             destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
             rewrite UIP_refl with (p := EQ₂); simpl; rewrite !UIP_refl with (p := EQ₁).
             clear EQ₁ EQ₂.
             do 2 eapply I_exists_intro;
             isplit; [reflexivity |];
             isplit; [reflexivity |].
             later_shift.
             genEQ HH.
             simpl.
             intros HH.
             rewrite UIP_refl with (p := HH); simpl.
             term_simpl.
             apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
             iright.
             do 2 eapply I_exists_intro;
             isplit; [reflexivity |];
             isplit; [reflexivity |].
             apply (I_fix_unroll _ _ RPR_contr); fold RP; simpl.
             apply H.
        * iintro u₁; iintro u₂; iintro H.
          idestruct H as H H.
          -- idestruct H as p H;
               idestruct H as m H;
               idestruct H as HH H.
             destruct HH as [-> ->].
             do 3 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             do 13 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
             match goal with
             | |- context G [_ ⊨ ECL ?a _ _] => set (T := a)
             end.
             apply (I_fix_unroll _ _ RPR_contr) in H; simpl in H.
             unfold viewG in H; simpl in H.
             destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
             rewrite UIP_refl with (p := EQ₂) in H; simpl in H; rewrite !UIP_refl with (p := EQ₁) in H.
             clear EQ₁ EQ₂.
             idestruct H as va H;
               idestruct H as vb H;
               idestruct H as Hva H;
               idestruct H as Hvb H.
             rewrite Hva, Hvb.
             do 2 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             apply (I_fix_unroll _ _ RPR_contr) in H; simpl in H.
             term_simpl in H.
             revert H.
             genEQ HH.
             simpl.
             intros HH.
             rewrite UIP_refl with (p := HH); simpl.
             clear HH; intros H.
             idestruct H as H H.
             ++ idestruct H as va' H;
                  idestruct H as vb' H;
                  idestruct H as Hva' H;
                  idestruct H as Hvb' H.
                rewrite Hva', Hvb'.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                do 4 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
                apply ECL_ret.
                subst T.
                iright.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [reflexivity |].
                isplit; [reflexivity | reflexivity].
             ++ idestruct H as va' H;
                  idestruct H as vb' H;
                  idestruct H as Hva' H;
                  idestruct H as Hvb' H.
                rewrite Hva', Hvb'.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                do 3 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
                apply ECL_ret.
                subst T.
                ileft.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [reflexivity |].
                isplit; [reflexivity | reflexivity].
          -- idestruct H as p H;
               idestruct H as m H;
               idestruct H as HH H.
             destruct HH as [-> ->].
             do 3 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             do 3 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
             match goal with
             | |- context G [_ ⊨ ECL ?a _ _] => set (T := a)
             end.
             apply (I_fix_unroll _ _ RPR_contr) in H; simpl in H.
             unfold viewG in H; simpl in H.
             destruct (kind_arr_inv eq_refl) as [EQ₁ EQ₂]; simpl.
             rewrite UIP_refl with (p := EQ₂) in H; simpl in H; rewrite !UIP_refl with (p := EQ₁) in H.
             clear EQ₁ EQ₂.
             idestruct H as va H;
               idestruct H as vb H;
               idestruct H as Hva H;
               idestruct H as Hvb H.
             rewrite Hva, Hvb.
             do 2 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
             apply (I_fix_unroll _ _ RPR_contr) in H; simpl in H.
             term_simpl in H.
             revert H.
             genEQ HH.
             simpl.
             intros HH.
             rewrite UIP_refl with (p := HH); simpl.
             clear HH; intros H.
             idestruct H as H H.
             ++ idestruct H as va' H;
                  idestruct H as vb' H;
                  idestruct H as Hva' H;
                  idestruct H as Hvb' H.
                rewrite Hva', Hvb'.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                do 14 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
                apply ECL_ret.
                subst T.
                iright.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [reflexivity |].
                isplit; [reflexivity | reflexivity].
             ++ idestruct H as va' H;
                  idestruct H as vb' H;
                  idestruct H as Hva' H;
                  idestruct H as Hvb' H.
                rewrite Hva', Hvb'.
                do 1 (eapply ECL_step'; [repeat constructor | econstructor 2; repeat constructor | term_simpl; later_shift]).
                do 14 (eapply ECL_step; [econstructor 2; repeat constructor | term_simpl]).
                apply ECL_ret.
                subst T.
                ileft.
                do 2 eapply I_exists_intro;
                isplit; [split; reflexivity |].
                isplit; [reflexivity |].
                isplit; [reflexivity | reflexivity].
  Qed.

End Counter.

Section FreeThm.

  Definition idf {X : Set} : value X
    := (Λ ƛ (v_var VZ))%syn.

  Fact idf_typ {X : Set} {Δ Ψ} {Γ : X -> typ KTyp Δ} : Δ ∣ Ψ ∣ Γ ⊢ᵥ idf : (∀ᵗ KTyp , 0ᵛ →ᵗ 0ᵛ)%typ.
  Proof.
    do 5 constructor; reflexivity.
  Qed.

  Lemma idf_free_thm' {X Δ Ψ Γ}
    : ∀ v : value X,
    Δ ∣ Ψ ∣ Γ ⊢ᵥ v : (∀ᵗ KTyp , 0ᵛ →ᵗ 0ᵛ)%typ ->
    (@ctx_approx X Δ Ψ Γ
       (e_val v)%syn
       (e_val idf)%syn
       (∀ᵗ KTyp , 0ᵛ →ᵗ 0ᵛ)%typ).
  Proof.
    intros e Hf.
    apply fl_val in Hf.
    apply adequacy.
    apply valT.
    intros η Hη HΨ γ γ' n Hγ.
    specialize (Hf η Hη HΨ γ γ' n Hγ).
    clear Hγ HΨ Hη Γ Ψ.
    term_simpl in Hf.
    apply (I_fix_unroll _ _ RPR_contr) in Hf; simpl in Hf.
    idestruct Hf as e₁ Hf;
      idestruct Hf as e₂ Hf;
      idestruct Hf as He₁ Hf;
      idestruct Hf as He₂ Hf.
    rewrite He₁.
    clear He₁ He₂.
    apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
    term_simpl.
    clear γ γ'.
    do 2 eapply I_exists_intro;
    isplit; [reflexivity |];
    isplit; [reflexivity |].
    iintro μ; iintro Hμ.
    term_simpl.
    rewrite map_id'.
    term_simpl in Hf.
    assert (Hf' : n
                   ⊨ ▷ (∀ᵢ μ : Neu KTyp ε,
                        (interpNeu μ η_id ≅ μ )ᵢ
                          ⇒ ECL (I_fix (∀ₛ (_ : gtyp) (_ _ : value ∅), *ₛ)%irel_sig RPR RPR_contr (viewG (neumap ı%bind μ →ᵗ μ)%U)) e₁ e₂)).
    {
      apply I_later_forall_up.
      iintro u.
      apply I_later_arrow_up.
      iintro Hu.
      ispecialize_forall Hf u (Neu KTyp ε) R.
      destruct n.
      - apply I_later_zero.
      - rewrite I_later_shift in Hu.
        apply I_Prop_elim in Hu.
        iapply Hf.
        apply Hu.
    }
    clear Hf; rename Hf' into Hf.
    later_shift.
    pose proof Hf as Hg.
    ispecialize_forall Hg (@neu_rel ε (fun (v₁ v₂ : value ∅) => (True)ᵢ)) (Neu KTyp ε) R.
    ispecialize Hg; [unfold interpNeu; reflexivity |].
    term_simpl in Hg.
    eapply ECL_safety in Hg.
    destruct Hg as [[m' [v [v'' [Hm' [Hs'' [Hs''' Hg]]]]]] | [m' [e' [Hj1 Hj2]]]].
    - apply ECL_safety2.
      left.
      exists m', v.
      eexists _.
      split; [assumption |].
      split; [assumption |].
      split; [constructor 1 |].
      apply (I_fix_roll _ _ RPR_contr); fold RP; simpl.
      iintro u1; iintro u2.
      ispecialize_forall Hf (@neu_rel ε (fun (v₁ v₂ : value ∅) => (v₁ = u1 ∧ v₂ = u2)ᵢ)) (Neu KTyp ε) R.
      ispecialize Hf; [unfold interpNeu; reflexivity |].
      eapply ECL_partial_correctness in Hf; [| eassumption | eassumption | eassumption].
      apply (I_fix_unroll _ _ RPR_contr) in Hf; simpl in Hf.
      ispecialize_forall Hf u1 (value ∅) R.
      ispecialize_forall Hf u2 (value ∅) R.
      ispecialize Hf; [split; reflexivity |].
      clear Hg Hs''' Hs'' Hm'.
      remember (n - m') as k eqn:Heqk.
      clear Heqk.
      clear m' n.
      iintro Hu.
      eapply ECL_safety in Hf.
      destruct Hf as [[m [t [t' [Hm [Hs [Hs' Hg]]]]]] | [m [t [Hj1 Hj2]]]].
      + apply (ex_intro (fun x => nsteps x _ _) m) in Hs.
        rewrite <-erased_steps_nsteps in Hs.
        eapply ECL_bigstep.
        apply Hs.
        eapply ECL_step; [econstructor 2; constructor | term_simpl].
        eapply ECL_ret.
        apply I_Prop_elim in Hg.
        destruct Hg as [Hg1 Hg2]; rewrite Hg1 at 1.
        apply Hu.
      + eapply ECL_diverge; [apply Hj1 | apply Hj2].
    - eapply ECL_diverge; [apply Hj1 | apply Hj2].
  Qed.

End FreeThm.
