Require IntDef.

Definition ltac_int_to_nat (x:BinNums.Z) : nat :=
  match x with
  | BinNums.Z0 => 0%nat
  | BinNums.Zpos p => PosDef.Pos.to_nat p
  | BinNums.Zneg p => 0%nat
  end.

Ltac number_to_nat N :=
  match type of N with
  | nat => constr:(N)
  | BinNums.Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  end.

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match number_to_nat N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.

Tactic Notation "dup" :=
  dup 2.
