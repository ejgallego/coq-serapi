Require Import List.
Import ListNotations.

Ltac break_match_hyp :=
  match goal with
    | [ H : context [ match ?X with _ => _ end ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match_goal :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac break_match := break_match_goal || break_match_hyp.

Ltac subst_max :=
  repeat match goal with
           | [ H : ?X = _ |- _ ]  => subst X
           | [H : _ = ?X |- _] => subst X
         end.

Ltac inv H := inversion H; subst_max.
Ltac invc H := inv H; clear H.
Ltac invcs H := invc H; simpl in *.

Ltac find_inversion :=
  match goal with
    | [ H : ?X _ _ _ _ _ _ = ?X _ _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ _ = ?X _ _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ _ = ?X _ _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ _ = ?X _ _ _ |- _ ] => invc H
    | [ H : ?X _ _ = ?X _ _ |- _ ] => invc H
    | [ H : ?X _ = ?X _ |- _ ] => invc H
  end.

Inductive Nth {A : Type} : list A -> nat -> A -> Prop :=
| Nth_0 : forall x l, Nth (x :: l) 0 x
| Nth_S : forall l x n y, Nth l n x -> Nth (y :: l) (S n) x.

Lemma nth_error_Nth :
  forall A n l (x : A),
    nth_error l n = Some x ->
    Nth l n x.
Proof.
  induction n; intros; simpl in *; auto.
  - break_match; try discriminate.
    unfold value in *.
    find_inversion.
    constructor.
  - break_match; try discriminate.
    subst. constructor.
    eauto.
Defined.

Lemma Nth_nth_error :
  forall A n l (x : A),
    Nth l n x ->
    nth_error l n = Some x.
Proof.
  intros.
  induction H; simpl in *; auto.
Defined.
