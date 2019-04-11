Require Import List.
Import ListNotations.

Fixpoint before {A: Type} (x : A) y l : Prop :=
  match l with
    | [] => False
    | a :: l' =>
      a = x \/
      (a <> y /\ before x y l')
  end.

Section before.
  Variable A : Type.

  Lemma before_In :
    forall x y l,
      before (A:=A) x y l ->
      In x l.
  Proof.
    induction l; intros; simpl in *; intuition.
  Qed.
End before.
