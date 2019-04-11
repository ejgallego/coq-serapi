Require Import OrderedType.
Require Import Structures.OrderedTypeEx.

Definition dyadic {A : Type} : Type := A + (A * A).

Inductive dyadic_lex_lt {A : Type} {lt : A -> A -> Prop} : dyadic -> dyadic -> Prop :=
| dyadic_lex_lt_t_t : forall (l l' : A), lt l l' -> dyadic_lex_lt (inl l) (inl l')
| dyadic_lex_lt_t_dyad : forall (l l1 l1': A), dyadic_lex_lt (inl l) (inr (l1, l1'))
| dyadic_lex_lt_dyad_lt : forall (l0 l0' l1 l1' : A), lt l0 l1 -> dyadic_lex_lt (inr (l0, l0')) (inr (l1, l1'))
| dyadic_lex_lt_dyad_eq : forall (l l0' l1' : A), lt l0' l1' -> dyadic_lex_lt (inr (l, l0')) (inr (l, l1')).

Module Type DyadicUsualOrderedType (UOT : UsualOrderedType) <: UsualOrderedType.
  Definition t := @dyadic UOT.t.
  Definition eq := @eq t.
  Parameter Inline lt : t -> t -> Prop.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End DyadicUsualOrderedType.
