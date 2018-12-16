Require Import List String Ascii.
Import ListNotations.

Local Open Scope char.

Module chars.
  Notation lparen := "("%char.
  Notation rparen := ")"%char.
  Notation space  := " "%char.
  Notation newline  := "010"%char.

  Definition reserved (a : ascii) : Prop  :=
    In a [lparen; rparen; newline; space].

  Definition reserved_dec (a : ascii) : {reserved a} + {~ reserved a}.
    unfold reserved.
    apply in_dec.
    apply ascii_dec.
  Defined.

  Lemma lparen_reserved : reserved lparen.
  Proof using. red. intuition. Qed.
End chars.
