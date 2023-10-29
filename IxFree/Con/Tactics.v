Require Import Utf8.
Require Import IxFree.Base.
Require Import IxFree.Con.Arrow.
Require Import IxFree.Con.Conj.
Require Import IxFree.Con.Disj.
Require Import IxFree.Con.Iff.
Require Import IxFree.Con.Forall.
Require Import IxFree.Con.Exists.
Require Import IxFree.Con.Later.
Require Arith.

Ltac unfold_headH P H :=
  match P with
  | ?P _ => unfold_headH P H
  | _ => first [progress simpl P at 1 in H | unfold P at 1 in H]
  end.

Ltac unfold_headG P :=
  match P with
  | ?P _ => unfold_headG P
  | _ => first [progress simpl P at 1 | unfold P at 1]
  end.

Ltac iintro_named H :=
  match goal with
  | |- ?n ⊨ ?P ⇒ ?Q       => iintro_arrow_named H
  | |- ?n ⊨ ∀ᵢ x : ?A, ?P => iintro_forall_named H
  | |- ?n ⊨ ?P            => unfold_headG P; iintro_named H
  | |- _  ⊨ ?P            => fail "Cannot coerce" P "to a universal quantifier or an arrow"
  end.

Ltac iintro_anon :=
  match goal with
  | |- ?n ⊨ ?P ⇒ ?Q        => iintro_arrow_anon
  | |- ?n ⊨ I_forall ?A ?P => iintro_forall_anon
  | |- ?n ⊨ ▷ ?P           => iintro_later
  | |- ?n ⊨ (?P)ᵢ          => idtac
  | |- ?n ⊨ ?P             => unfold_headG P; iintro_anon
  | |- _  ⊨ ?P             => fail "Cannot coerce" P "to an introducible type"
  end.

Tactic Notation "iintro" ident(H) := iintro_named H; isimplP.
Tactic Notation "iintro" := iintro_anon; isimplP.

Ltac iapply_goal H :=
  first [exact H | eexact H
        | let T := type of H in
          match T with
          | _ ⊨ ?P => iapply_goal_aux H T P
          | _ => iapply_goal_aux H T T
          end]
with iapply_goal_aux H P T :=
    match P with
    | ?P → ?Q =>
      let J := fresh in
      assert (J : P); [| specialize (H J); iapply_goal H; clear J]
    | ∀ x : ?A, ?P =>
      let y := fresh x in
      evar (y : A); specialize (H y); iapply_goal H; subst y
      (*generalize dependent y; cbv zeta; intros*)
    | ?n ⊨ ?P ⇒ ?Q =>
      let J := fresh H in
      assert (J : n ⊨ P);
      [| apply (I_arrow_elim H) in J; iapply_goal J; clear J]
    | ?n ⊨ I_forall ?A ?P =>
      eapply I_forall_elim in H;
      iapply_goal H
    | ?n ⊨ (?P)ᵢ =>
      apply I_Prop_elim in H; eapply H
    | ?n ⊨ ?P =>
      tryif unfold_headH P H then let Q := type of H in iapply_goal_aux H Q T
      else fail 99 "Cannot match" T "as a function or universal quantifier"
    end.

Ltac iapply_goal_wrap H :=
  let J := fresh in assert (J := H); iapply_goal J; clear J; isimplP.

Ltac iapply_hyp_aux H1 H2 P2 T :=
  match type of H1 with
  | ?n ⊨ ?P1 ⇒ ?Q =>
    first [apply (I_arrow_elim H1) in H2
          |
          (*tryif change P1 with P2 in H1 then apply (I_arrow_elim H1) in H2 else*)
          let J := fresh H1 in
         assert (J : n ⊨ P1);
         [| apply (I_arrow_elim H1) in J; iapply_hyp_aux J H2 P2 Q; clear J]]
  | _ ⊨ I_forall ?A ?P1 =>
    eapply I_forall_elim in H1; iapply_hyp_aux H1 H2 P2 P1
  | _ ⊨ ?P1 =>
    tryif unfold_headH P1 H1 then iapply_hyp_aux H1 H2 P2 T
    else fail 99 "Cannot match" T "as a function or universal quantifier"
  end.

Ltac iapply_hyp H1 H2 :=
  let J := fresh in assert (J := H1);
  match type of H2 with
  | ?n ⊨ ?P2 => match type of H1 with
                | n ⊨ ?T => iapply_hyp_aux J H2 P2 T
                end
  end;
  clear J;
  isimplP.

Tactic Notation "iapply" constr(H) := iapply_goal_wrap H.
Tactic Notation "iapply" constr(H1) "in" ident(H2) := iapply_hyp H1 H2.

Ltac iespecialize H :=
  repeat (eapply I_forall_elim in H).

Ltac ispecialize_arrow H :=
  let T := type of H in
  match T with
  | (?N ⊨ ?P ⇒ ?Q) =>
    let J := fresh in
    assert (J : N ⊨ Q); [ iapply H | clear H; rename J into H ]
  end.

Ltac ispecialize_forall H X TX R :=
  let T := type of H in
  match T with
  | (?N ⊨ I_forall ?A ?P) =>
    tryif change A with TX in H then
      let J := fresh
      in assert (J := I_forall_elim H X); clear H; try (cbv beta in J); rename J into H
    else fail 99 "Cannot coerce" TX "to" A
  | (?n ⊨ ?P) =>
    tryif unfold_headH P H then ispecialize_forall H X TX R
    else fail 99 "Cannot coerce" R "to a universal quantifier"
  end.

Ltac ispecialize_choose H X :=
  match type of H with
  | _ ⊨ ?T =>
    let TX := type of X
    in match TX with
       | _ ⊨ ?P => ispecialize_arrow H; [exact X |]
       | _ => ispecialize_forall H X TX T
       end
  end.

Tactic Notation "ispecialize" hyp(H) := ispecialize_arrow H; isimplP.
Tactic Notation "ispecialize" hyp(H) constr(X) := ispecialize_choose H X; isimplP.

Ltac gen_in_goal :=
  match goal with
  | |- (?n ⊨ ?P) → (?n ⊨ ?Q) => apply I_arrow_elim
  | |- ?P → ?n ⊨ ?Q =>
    match type of P with
    | Prop => let H := fresh "H" in
              intro H; apply (I_Prop_intro P n) in H;
              revert H; apply I_arrow_elim
    | _ => apply I_forall_elim
    end
  | |- ∀ x : ?Q, ?n ⊨ ?P =>
    let H := fresh "H" in assert (H : n ⊨ ∀ᵢ x : Q, P); [| now apply I_forall_elim, H]
  end.

Ltac igen H n := generalize H as n; gen_in_goal.
Ltac igen_anon t := generalize t; gen_in_goal.

Ltac irev_aux :=
  match goal with
  | |- ?n ⊨ ?P => idtac
  | |- ∀ x, ?P => intros x; irev_aux; revert x; gen_in_goal
  end.

Tactic Notation "igeneralize" constr(t) := igen_anon t.
Tactic Notation "igeneralize" constr(t) "as" ident(n) := igen t n.
Tactic Notation "irevert" hyp_list(xs) := revert xs; irev_aux.

Tactic Notation "idestruct" hyp(H) "as" ident(x) ident(y) :=
  (idestruct_conj H x y || idestruct_disj H x y || idestruct_exists H x y); isimplP.

(* ========================================================================= *)
(* Tactics for ▷ *)

Lemma I_later_arrow_up {n : nat} {P Q : IProp} :
  (n ⊨ ▷P ⇒ ▷Q) → (n ⊨ ▷(P ⇒ Q)).
Proof.
intro H; destruct n; [ apply I_later_zero | apply I_later_shift ].
apply I_arrow_intro; intros k Hle HP.
apply I_later_shift; eapply I_arrow_elim.
  eapply I_valid_monotone; [ | eassumption ].
  apply Le.le_n_S; eassumption.
apply I_later_shift; assumption.
Qed.

Lemma I_later_forall_up {n : nat} {A : Type} {P : A → IProp} :
  (n ⊨ ∀ᵢ x, ▷ P x) → (n ⊨ ▷ ∀ᵢ x, P x).
Proof.
intro H; destruct n; [ apply I_later_zero | apply I_later_shift ].
iintro x; eapply I_forall_elim in H.
apply I_later_shift; eassumption.
Qed.

Ltac later_down :=
  match goal with
  | [ |- _ ⊨ ▷ I_forall _ _ ] => apply I_later_forall_up
  | [ |- _ ⊨ ▷(_ ⇒ _) ] => apply I_later_arrow_up
  end.

Lemma I_later_arrow_down {n : nat} {P Q : IProp} :
  (n ⊨ ▷(P ⇒ Q)) → (n ⊨ ▷P ⇒ ▷Q).
Proof.
intro H; iintro HP; later_shift.
iapply H; assumption.
Qed.

Lemma I_later_iff_down {n : nat} {P Q : IProp} :
  (n ⊨ ▷(P ⇔ Q)) → (n ⊨ ▷P ⇔ ▷Q).
Proof.
intro H; isplit; apply I_later_arrow_down; later_shift;
  iintro; apply I_iff_elim_M in H; apply H; assumption.
Qed.

Lemma I_later_forall_down {n : nat} {A : Type} {P : A → IProp} :
  (n ⊨ ▷ ∀ᵢ x, P x) → (n ⊨ ∀ᵢ x, ▷ P x).
Proof.
intro H; iintro x; later_shift; iapply H.
Qed.

Ltac later_up := 
  match goal with
  | [ |- _ ⊨ _ ⇒ _ ] => apply I_later_arrow_down
  | [ |- _ ⊨ I_forall _ _ ] => apply I_later_forall_down
  | [ |- _ ⊨ _ ⇔ _ ] => apply I_later_iff_down
  end.