Require Import Utf8.
Require Import Binding.Lib.
Require Import RelationClasses Morphisms.

Local Open Scope bind_scope.

Section Functors.
  Context {Obj : Type}.
  
  Class EqInd1 (F : Obj → Type) :=
    eq1 : ∀ {A : Obj}, F A → F A → Prop.

  Class EquivInd1 (F : Obj → Type) {EI : EqInd1 F} : Prop :=
    eq1_equiv : ∀ {A : Obj}, Equivalence (eq1 (A := A)).

  Context {Arr : Obj → Obj → Type} {ArrEq : EqIndCore Arr} {AC : ArrowCore Arr}.

  Class FunctorEq (F : Obj → Type) {EI : EqInd1 F} {FunCore : FunctorCore F} : Prop :=
    { fmap_ext {A B} :> Proper (equal A B ==> eq1 (A := A) ==> eq1 (A := B)) fmap;
      fmap_ı {A} (v : F A) : eq1 (fmap ı v) v;
      fmap_comp {A B C} (δ₂ : Arr B C) (δ₁ : Arr A B) (v : F A) :
        eq1 (fmap δ₂ (fmap δ₁ v)) (fmap (δ₂ ∘ δ₁) v)
    }.

  Context {EIA : EqInd Arr} {AA : Arrow Arr}.

  #[export] Instance Fun_Eq (F : Obj → Type) {FC : FunctorCore F} {FF : Functor F}  :
    FunctorEq F (EI := λ A, @eq (F A)).
  Proof.
    split; intros.
    - intros δ₁ δ₂ EQδ v v' EQv; unfold eq1 in *; simpl; subst v'; now rewrite EQδ.
    - unfold eq1; apply map_id'.
    - unfold eq1; apply map_map_comp'.
  Qed.

  #[export] Instance EI1_equiv (F : Obj → Type) {EI : EqInd1 F} {EQI : EquivInd1 F} {A : Obj} : Equivalence (eq1 (A := A)) := eq1_equiv (A := A).

  Record PShf :=
    { FO     :> Obj → Type;
      Peq    :  EqInd1 FO;
      Pequiv :  EquivInd1 FO;
      FA     :  FunctorCore (Arr := Arr) FO;
      Pfun   :  FunctorEq FO
    }.

  #[export] Instance PShf_eq {X : PShf} : EqInd1 (FO X) := Peq X.
  #[export] Instance PShf_equiv {X : PShf} : EquivInd1 (FO X) := Pequiv X.
  #[export] Instance PShf_funcore {X : PShf} : FunctorCore (FO X) := FA X.
  #[export] Instance PShf_functor {X : PShf} : FunctorEq (FO X) := Pfun X.
  
End Functors.
Arguments PShf Obj {Arr ArrEq AC}.
Arguments PShf_funcore {Obj Arr ArrEq AC X} /.

Notation "u ≅ v" := (eq1 u v) (at level 70, no associativity).

Section Arrows.
  Context {Obj : Type}.
  Context {Arr : Obj → Obj → Type} {ArrEq : EqIndCore Arr} {AC : ArrowCore Arr}.

  Class FComp {X Y : PShf Obj} {A} (K : ∀ {B}, (Arr A B) → X B → Y B) :=
    comp_fmap : ∀ {B C} (δ₂ : Arr B C) (δ₁ : Arr A B) (v : X B),
        K (δ₂ ∘ δ₁) (fmap δ₂ v) ≅ fmap δ₂ (K δ₁ v).

  Record RemFun (X Y : PShf Obj) (A : Obj) :=
    { arr :> ∀ {B}, (Arr A B) → X B → Y B;
      arr_ext {B} : Proper (equal A B ==> eq1 (A := B) ==> eq1 (A := B)) arr;
      arr_fmap : FComp (@arr)
        (*{B C} (δ₂ : Arr B C) (δ₁ : Arr A B) (v : X B) :
        arr (δ₂ ∘ δ₁) (fmap δ₂ v) ≅ fmap δ₂ (arr δ₁ v)*)
    }.
  Arguments arr {X Y A} _ {B} _ _.

  #[export] Instance RF_prop {X Y : PShf Obj} {A} {RF : RemFun X Y A} {B} :
    Proper (equal A B ==> eq1 (A := B) ==> eq1 (A := B)) (RF B) :=
    arr_ext _ _ _ RF.

  #[export] Instance RF_FComp {X Y : PShf Obj} {A} {RF : RemFun X Y A} :
    FComp RF := arr_fmap _ _ _ RF.

  #[export] Instance EqInd_Arr {X Y : PShf Obj} : EqInd1 (RemFun X Y) :=
    λ {A} φ₁ φ₂, ∀ {B} (δ : Arr A B) v, φ₁ _ δ v ≅ φ₂ _ δ v.

  #[export] Instance EquivInd_Arr {X Y : PShf Obj} : EquivInd1 (RemFun X Y).
  Proof.
    split.
    - intros φ B δ v; reflexivity.
    - intros φ₁ φ₂ EQφ B δ v; symmetry; apply EQφ.
    - intros φ₁ φ₂ φ₃ EQφ₁ EQφ₂ B δ v; etransitivity; [apply EQφ₁ | apply EQφ₂].
  Qed.

  Context {EIA : EqInd Arr} {AA : Arrow Arr}.

  #[export] Program Instance FC_Arr {X Y : PShf Obj} : FunctorCore (Arr := Arr) (RemFun X Y) :=
    λ {A B} δ φ, {| arr C δ' v := φ C (δ' ∘ δ) v |}.
  Next Obligation.
    rename B0 into C; intros δ₁ δ₂ EQδ v₁ v₂ EQv; now rewrite EQδ, EQv.
  Qed.
  Next Obligation.
    unfold FComp; intros; rewrite arrow_comp_assoc; apply arr_fmap.
  Qed.
    
  #[export] Instance Fun_Arr {X Y : PShf Obj} : FunctorEq (RemFun X Y).
  Proof.
    split.
    - intros A B δ₁ δ₂ EQδ φ₁ φ₂ EQφ C δ v; simpl; now rewrite EQδ.
    - intros A φ B δ v; simpl; now rewrite arrow_comp_id_r.
    - intros A B C δ₂ δ₁ φ D δ v; simpl; now rewrite arrow_comp_assoc.
  Qed.

  Definition PArr (X Y : PShf Obj) : PShf Obj :=
    {| FO  := RemFun X Y;
       Peq := EqInd_Arr;
       FA  := FC_Arr
    |}.

  #[export] Instance arr_proper {X Y A} : Proper (eq1 ==> forall_relation (λ B, equal A B ==> eq1 ==> eq1)) (@arr X Y A).
  Proof.
    intros φ₁ φ₂ EQφ B δ₁ δ₂ EQδ a₁ a₂ EQa; rewrite EQδ, EQa; apply EQφ.
  Qed.    
  
End Arrows.

Notation "'λₖ' Δ δ μ , e" := {| arr Δ δ μ := e; arr_ext := _; arr_fmap := _ |} (at level 120, Δ binder, δ binder, μ binder, no associativity).

Arguments fmap {_ _ _ _ _ _} _ !_.
Arguments arrow_comp : simpl never.
Arguments arrow_id : simpl never.
