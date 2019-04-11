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

Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
    | [ H : context [ if ?X then _ else _ ] |- _] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac find_higher_order_rewrite :=
  match goal with
    | [ H : _ = _ |- _ ] => rewrite H in *
    | [ H : forall _, _ = _ |- _ ] => rewrite H in *
    | [ H : forall _ _, _ = _ |- _ ] => rewrite H in *
  end.

Fixpoint assoc {K V}
 (K_eq_dec : forall k k' : K, {k = k'} + {k <> k'})
 (l : list (K * V)) (k : K) : option V :=
  match l with
    | [] => None
    | (k', v) :: l' =>
      if K_eq_dec k k' then
        Some v
      else
        assoc K_eq_dec l' k
  end.

Definition assoc_default {K V}
 (K_eq_dec : forall k k' : K, {k = k'} + {k <> k'})
 (l : list (K * V)) (k : K) (default : V) : V :=
  match (assoc K_eq_dec l k) with
    | Some x => x
    | None => default
  end.

Fixpoint assoc_set {K V}
 (K_eq_dec : forall k k' : K, {k = k'} + {k <> k'})
 (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
  match l with
    | [] => [(k, v)]
    | (k', v') :: l' =>
      if K_eq_dec k k' then
        (k, v) :: l'
      else
        (k', v') :: (assoc_set K_eq_dec l' k v)
  end.

Fixpoint assoc_del {K V}
 (K_eq_dec : forall k k' : K, {k = k'} + {k <> k'})
 (l : list (K * V)) (k : K) : list (K * V) :=
  match l with
    | [] => []
    | (k', v') :: l' =>
      if K_eq_dec k k' then
        assoc_del K_eq_dec l' k
      else
        (k', v') :: (assoc_del K_eq_dec l' k)
  end.

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

Ltac find_rewrite :=
  match goal with
    | [ H : ?X _ _ _ _ = _, H' : ?X _ _ _ _ = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : ?X = _ |- _ ] => rewrite H in H'
    | [ H : ?X = _, H' : context [ ?X ] |- _ ] => rewrite H in H'
    | [ H : ?X = _ |- context [ ?X ] ] => rewrite H
  end.

Lemma get_set_same :
  forall K V K_eq_dec k v (l : list (K * V)),
    assoc K_eq_dec (assoc_set K_eq_dec l k v) k = Some v.
Proof.
  induction l; intros; simpl; repeat (break_match; simpl); subst; congruence.
Qed.

Lemma get_set_same' :
  forall K V K_eq_dec k k' v (l : list (K * V)),
    k = k' ->
    assoc K_eq_dec (assoc_set K_eq_dec l k v) k' = Some v.
Proof.
  intros. subst. auto using get_set_same.
Qed.

Lemma get_set_diff :
  forall K V K_eq_dec k k' v (l : list (K * V)),
    k <> k' ->
    assoc K_eq_dec (assoc_set K_eq_dec l k v) k' = assoc K_eq_dec l k'.
Proof.
  induction l; intros; simpl; repeat (break_match; simpl); subst; try congruence; auto.
Qed.

Lemma not_in_assoc :
  forall K V K_eq_dec k (l : list (K * V)),
    ~ In k (map (@fst _ _) l) ->
    assoc K_eq_dec l k = None.
Proof.
  intros.
  induction l.
  - auto.
  - simpl in *. repeat break_match; intuition.
    subst. simpl in *. congruence.
Qed.

Lemma get_del_same :
  forall K V K_eq_dec k (l : list (K * V)),
    assoc K_eq_dec (assoc_del K_eq_dec l k) k = None.
Proof.
  induction l; intros; simpl in *.
  - auto.
  - repeat break_match; subst; simpl in *; auto.
    break_if; try congruence.
Qed.

Lemma get_del_diff :
  forall K V K_eq_dec k k' (l : list (K * V)),
    k <> k' ->
    assoc K_eq_dec (assoc_del K_eq_dec l k') k = assoc K_eq_dec l k.
Proof.
  induction l; intros; simpl in *.
  - auto.
  - repeat (break_match; simpl); subst; try congruence; auto.
Qed.

Lemma get_set_diff_default :
  forall K V K_eq_dec (k k' : K) (v : V) l d,
    k <> k' ->
    assoc_default K_eq_dec (assoc_set K_eq_dec l k v) k' d = assoc_default K_eq_dec l k' d.
Proof.
  unfold assoc_default.
  intros.
  repeat break_match; auto;
  rewrite get_set_diff in * by auto; congruence.
Qed.

Lemma get_set_same_default :
  forall K V K_eq_dec (k : K) (v : V) l d,
    assoc_default K_eq_dec (assoc_set K_eq_dec l k v) k d = v.
Proof.
  unfold assoc_default.
  intros.
  repeat break_match; auto;
  rewrite get_set_same in *; congruence.
Qed.

Lemma assoc_assoc_default:
  forall K V K_eq_dec l (k : K) (v : V) d,
    assoc K_eq_dec l k = Some v ->
    assoc_default K_eq_dec l k d = v.
Proof.
  intros. unfold assoc_default.
  break_match; congruence.
Qed.

Lemma assoc_assoc_default_missing:
  forall K V K_eq_dec (l : list (K * V)) k d,
    assoc K_eq_dec l k = None ->
    assoc_default K_eq_dec l k d = d.
Proof using.
  intros. unfold assoc_default.
  break_match; congruence.
Qed.

Lemma assoc_set_same :
  forall K V K_eq_dec (l : list (K * V)) k v,
    assoc K_eq_dec l k = Some v ->
    assoc_set K_eq_dec l k v = l.
Proof.
  intros. induction l; simpl in *; auto; try congruence.
  repeat break_match; simpl in *; intuition.
  - subst. find_inversion. auto.
  - repeat find_rewrite. auto.
Qed.

Lemma assoc_default_assoc_set :
  forall K V K_eq_dec l (k : K) (v : V) d,
    assoc_default K_eq_dec (assoc_set K_eq_dec l k v) k d = v.
Proof.
  intros. unfold assoc_default.
  rewrite get_set_same. auto.
Qed.

Lemma assoc_set_assoc_set_same :
  forall K V K_eq_dec l (k : K) (v : V) v',
    assoc_set K_eq_dec (assoc_set K_eq_dec l k v) k v' = assoc_set K_eq_dec l k v'.
Proof.
  induction l; intros; simpl in *; repeat break_match; simpl in *; subst; try congruence; eauto;
break_if; congruence.
Qed.

Definition a_equiv {K V} K_eq_dec (l1 : list (K * V)) l2 :=
  forall k,
    assoc K_eq_dec l1 k = assoc K_eq_dec l2 k.

Lemma a_equiv_refl :
  forall K V K_eq_dec (l : list (K * V)),
    a_equiv K_eq_dec l l.
Proof using.
  intros. unfold a_equiv. auto.
Qed.

Lemma a_equiv_sym :
  forall K V K_eq_dec (l l' : list (K * V)),
    a_equiv K_eq_dec l l' ->
    a_equiv K_eq_dec l' l.
Proof.
  unfold a_equiv. intros. auto.
Qed.

Lemma a_equiv_trans :
  forall K V K_eq_dec (l l' l'' : list (K * V)),
    a_equiv K_eq_dec l l' ->
    a_equiv K_eq_dec l' l'' ->
    a_equiv K_eq_dec l l''.
Proof.
  unfold a_equiv in *.
  intros. repeat find_higher_order_rewrite.
  auto.
Qed.

Ltac assoc_destruct :=
  match goal with
  | [ |- context [assoc ?eq_dec (assoc_set ?eq_dec _ ?k0' _) ?k0 ] ] =>
    destruct (eq_dec k0 k0'); [subst k0'; rewrite get_set_same with (k := k0)|
                                 rewrite get_set_diff with (k' := k0) by auto]
  end.

Ltac assoc_rewrite :=
  match goal with
  | [  |- context [assoc _ (assoc_set _ _ ?k0' _) ?k0 ] ] =>
    first [rewrite get_set_same with (k := k0) by auto |
           rewrite get_set_diff with (k' := k0) by auto ]
  end.

Lemma assoc_set_assoc_set_diff :
  forall K V K_eq_dec l (k : K) (v : V) k' v',
    k <> k' ->
    a_equiv K_eq_dec (assoc_set K_eq_dec (assoc_set K_eq_dec l k v) k' v')
            (assoc_set K_eq_dec (assoc_set K_eq_dec l k' v') k v).
Proof.
  unfold a_equiv.
  intros.
  assoc_destruct.
  - now repeat assoc_rewrite.
  - assoc_destruct.
    + now repeat assoc_rewrite.
    + now repeat assoc_rewrite.
Qed.

Lemma a_equiv_nil :
  forall K V K_eq_dec (l : list (K * V)),
    a_equiv K_eq_dec l [] ->
    l = [].
Proof.
  intros.
  destruct l; auto.
  unfold a_equiv in *. simpl in *.
  destruct p.
  specialize (H k).
  break_if; try congruence.
Qed.

Lemma assoc_set_a_equiv :
  forall K V K_eq_dec l l' (k : K) (v : V),
    a_equiv K_eq_dec l l' ->
    a_equiv K_eq_dec (assoc_set K_eq_dec l k v) (assoc_set K_eq_dec l' k v).
Proof.
  unfold a_equiv.
  intros.
  assoc_destruct; assoc_rewrite; auto.
Qed.

Lemma assoc_default_a_equiv :
  forall K V K_eq_dec l l' (k : K) (v : V),
    a_equiv K_eq_dec l l' ->
    assoc_default K_eq_dec l k v = assoc_default K_eq_dec l' k v.
Proof.
  intros. unfold a_equiv, assoc_default in *.
  find_higher_order_rewrite.
  auto.
Qed.

Lemma assoc_a_equiv :
  forall K V K_eq_dec (l : list (K * V)) l' k,
    a_equiv K_eq_dec l l' ->
    assoc K_eq_dec l k = assoc K_eq_dec l' k.
Proof.
  unfold a_equiv.
  auto.
Qed.

Lemma assoc_default_assoc_set_diff :
  forall K V K_eq_dec (l : list (K * V)) k v k' d,
    k <> k' ->
    assoc_default K_eq_dec (assoc_set K_eq_dec l k' v) k d =
    assoc_default K_eq_dec l k d.
Proof.
  intros. unfold assoc_default. rewrite get_set_diff; auto.
Qed.
