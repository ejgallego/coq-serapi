## Coq Se(xp)rialized Protocol

This repository provides facilities to serialize Coq's Ml API and protocol to/from S-expressions.

SerAPI is a proof of concept and thus very unstable. It is meant to gather further feedback from coq IDE users and developers, comments
are very welcome!

### Quick demo

```
coq-serapi$ rlwrap ./ser_top.byte -prelude /home/egallego/external/coq-git/
(Print (CoqConstr (App (Rel 0) ((Rel 0)))))
> (Answer 0 Ack)
> (Answer 0(ObjList((CoqString"(_UNBOUND_REL_0 _UNBOUND_REL_0)"))))
(Control (StmQuery 2 "Print nat. "))
> (Answer 1 Ack)
> (Feedback((id(State 2))(contents Processed)(route 0)))
> (Feedback((id(State 0))(contents(Message ....))))
(Print (CoqRichpp (Element ....)))
> (Answer 2 Ack)
> (Answer 2(ObjList((CoqString"Inductive nat : Set :=  O : nat | S : nat -> nat\n\nFor S: Argument scope is [nat_scope]"))))
(Control StmState)
> (Answer 3 Ack)
> (Answer 3(StmInfo 2))
(Control (StmAdd 2 "Goal forall n, n + 0 = n."))
> (Answer 4 Ack)
> (Answer 4(StmInfo 4))
(Control (StmObserve 4))
> (Answer 5 Ack)
> (Feedback((id(State 4))(contents(ProcessingIn master))(route 0)))
> ...
(Query (None PpStr) Goals)
> (Answer 6 Ack)
> (Answer 6(ObjList((CoqString"forall n : nat, n + 0 = n"))))
(Query (None PpSexp) Goals)
> (Answer 7 Ack)
> (Answer 7(ObjList((CoqGoal()(CProdN((fname"")....))))))
(Control (StmAdd 4 "now induction n."))
> (Answer 8 Ack)
> (Answer 8(StmInfo 5))
(Control (StmObserve 5))
> (Answer 10 Ack)
> (Feedback((id(State 5))(contents Processed)(route 0)))
> ...
(Query (None PpStr) Goals)
> (Answer 11 Ack)
> (Answer 11(ObjList()))

```

Look into `ser_protocol.ml` for more details about the protocol itself.

### Building

OPAM and ocamlbuild are required. You need the following packages:

- ocamlfind
- ppx_import
- sexplib
- ppx_sexp_conv

Edit `myocamlbuild.ml` to add the location of Coq and opam
sources. Then, make should do the rest.

### Roadmap

_Version 0.02_:

 - Serialization of the `Proof.proof` object.
 - Improve API: options and workers.
 - Port CoqIDE to SerAPI. See tree at https://github.com/ejgallego/coqide-exp

### Technical details

Coq SerAPI has two main components:

- `serialize` a library providing automatic de/serialization of most Coq data structures using ppx_conv_sexp. This should be eventually incorporated into Coq itself.

- `sertop`, a toplevel implementing an modified version of the current IDE protocol. This is a simple file and largely independent of Coq itself.

Building your own toplevels using `serialize` is encouraged. Here, the current limit is the Ml API itself.

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.
