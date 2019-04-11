Require Import List.
Import ListNotations.

Polymorphic Inductive Nth {A : Type} : list A -> nat -> A -> Prop :=
| Nth_0 : forall x l, Nth (x :: l) 0 x
| Nth_S : forall l x n y, Nth l n x -> Nth (y :: l) (S n) x.

Lemma Nth_nth_error :
  forall A n l (x : A),
    Nth l n x ->
    nth_error l n = Some x.
Proof.
  intros.
  induction H; simpl in *; auto.
Defined.
