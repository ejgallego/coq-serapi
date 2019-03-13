Require Import List.
Require Import NArith.

Module Type OrderedTypeAlt.
 Parameter t : Type.

 Parameter compare : t -> t -> comparison.
 Infix "?=" := compare (at level 70, no associativity).

 Parameter compare_sym : forall x y, (y?=x) = CompOpp (x?=y).
 Parameter compare_trans : forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
 Parameter reflect : forall x y, x ?= y = Eq -> x = y.
End OrderedTypeAlt.

Module Nat_as_OTA <: OrderedTypeAlt.
  Definition t := nat.
  Fixpoint compare x y := 
    match x,y with 
      | O,O => Eq
      | O,_ => Lt
      | _,O => Gt
      | S x, S y => compare x y
    end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y). 
  Proof using. induction x; intros y; destruct y; simpl; auto. Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c. 
  Proof using.
    intros c x. revert c.
    induction x; intros c y z; destruct y; simpl; intro H; auto; subst; try discriminate H;
      destruct z; simpl; intro H'; eauto; try discriminate H'.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof using. induction x; intros y; destruct y; simpl; intro H; auto; discriminate. Qed.
End Nat_as_OTA.
