Unset Elimination Schemes.

Polymorphic Inductive Fl (A : Type) : Prop := .

Definition Fl_ind : forall (A : Type) (P : Prop), Fl A -> P :=
fun (A : Type) (P : Prop) (f : Fl A) => match f return P with end.
