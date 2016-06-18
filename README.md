## The Coq Se(xp)rialized Protocol

SerAPI is a new library and communication protocol for the Coq proof
assistant. It is based on automatic serialization of Ocaml datatypes
from/to S-expressions. SerAPI's main user base are IDE/tool
developers, however it is also fun to play with it, and serve as an
interesting debug tool for Coq. Its main design principles are:

- **Don't Repeat Yourself**: We build on top of Coq's plugin API, we have canonical commands (search, print).
- **Be extremely robust**: Any crash is a **critical** bug; we are liberal in what we accept, and strict in what we produce.
- **Make life easy**: We are flexible with abstractions in order to provide a user-oriented interface.

SerAPI is still a proof-of-concept. Feedback from Coq users and developers is very welcome, contact us by mail or in the issue tracker!

### Quick Overview and Documentation

SerAPI installation is similar to a Coq plugin, we hope to provide an OPAM package soon; for now, see [building](#building).

A first IDE prototype using SerAPI is Clément Pit--Claudel's [elcoq](https://github.com/cpitclaudel/elcoq).

To use SerAPI at a lower level, we provide a _SerTop toplevel_: `sertop.native`. The toplevel reads and writes commands (S-exps) from stdin/stdout. We recommend using our [emacs mode](sertop.el) or the `rlwrap` utility. `sertop.native --help` will provide an overview of command line options. `Ctrl-C` will interrupt a busy Coq process in a similar way than what `coqtop` does.

#### Protocol

SerAPI's main building block is the [`CoqObject`](sertop/sertop_protocol.mli#L22) data type, a _sum type_ encapsulating most core Coq objects.

**API WARNING:** _Object packing will change in the future, however adapting should be straightforward_.

Interaction happens by means of _commands_, which can be optionally tagged in the form of `(tag cmd)`; otherwise, an automatic tag will be assigned.
For every command, SerAPI **will always** reply with `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are four categories of commands:

- `(Control `[`control_cmd`](sertop/sertop_protocol.mli#L73)`)`: control commands are similar to a function call and instruct Coq to perform some action.
  Typical actions are to check a proof, set an option, modify a `load path`, etc... Every command will produce zero or more different _tagged_ [answers](sertop/sertop_protocol.mli#52), and  a final answer `(Answer tag Completed)`, indicating that there won't be more output.

  We assume the reader familiar with Coq's STM, [here](https://github.com/ejgallego/jscoq/blob/master/notes/coq-notes.md) and [here](https://github.com/siegebell/vscoq/blob/master/CoqProtocol.md) you can find a few informal notes on how it works, but we are documenting some of our extensions. See the issue tracker for more details.

- `(Query ((opt value) ...) kind)`:
  **API WARNING:** The Query API format is experimental and will change soon.

  Queries stream Coq objects of type `kind`. This can range from options, goals and hypotheses, tactics, etc... The first argument is a list of options: `preds` is a list of conjunctive filters, `limit` specifies how many values the query may return. `pp` controls the output format: `PpSexp` for full serialization, or `PpStr` for "pretty printing". For instance:
   ```lisp
   (tag (Query ((preds (Prefix "Debug")) (limit 10) (pp PpSexp)) Option))
   ```
   will stream all Coq options that start with "Debug", limiting to the first 10 and printing the full internal Coq datatype:
   ```lisp
   (CoqOption (Default Goal Selector)
      ((opt_sync true) (opt_depr false) (opt_name "default goal selector")
      (opt_value (StringValue 1))))
   ...
   ```
  Options can be omitted, as in: `(tag (Query ((limit 10)) Option))`, and
  currently supported queries can be seen [here](sertop/sertop_protocol.mli#L118)

- `(Print opts obj)`: The `Print` command provides access to the Coq pretty printers. Its intended use is for printing (maybe IDE manipulated) objects returned by `Query`.

- `(Parse num string)`: The `Parse` command gives access to the Coq parsing engine. We currently support detecting the end of the first num sentences, returning the corresponding `CoqPosition` objects. If you want to parse a document use the `StmAdd` control command instead.

Look at the [interface file](sertop/sertop_protocol.mli) more the details. The Ocaml type definitions are often self-explanatory and are serialized in a predictable way.

### Building

_The build system is work in progress. coq/coq#187 needs to be completed before we upload SerAPI to Opam._

Building `sertop` requires OPAM and Coq trunk.

1. Install the needed packages:
   `$ opam install ocamlfind ppx_import cmdliner core_kernel sexplib ppx_sexp_conv`
2. Download and compile coq trunk. We recommend:
   `$ ./configure -local && make -j $NJOBS`
3. Edit the `myocamlbuild.ml` file to add the location of your Coq sources.
4. `make` should build `sertop`.

### Emacs mode

Open `sertop.el` and run `M-x eval-buffer` followed by `M-x sertop` to get a sertop REPL in Emacs, with highlighting and pretty-printing (useful for debugging).

You may want to configure the variable `sertop-coq-directory` to point out the location of Coq's stdlib.

### Roadmap/Changelog:

_Version 0.02_:

 - **[done]** Serialization of the `Proof.proof` object.
 - **[done]** Improve API: add options.
 - **[done]** Improve and review printing workflow.
 - **[done]** `(Query ((Prefix "add") (Limit 10) (PpStr)) $ObjectType)`
 - **[done]** Basic Sentence splitting `(Parse num string))`, retuns the first num end of the sentences _without_ executing them.
   This has pitfalls as parsing is very stateful.
 - **[done]** Basic completion-oriented Search support `(Query () Names)`
 - **[done]** Better command line parsing (`Cmdliner`, `Core` ?)
 - **[partial]** Print Grammar tactic. `(Query ... (Tactics))`.
   Still we need to decide on:
   `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of
   `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs

_Version 0.03_:

 - **[done]** Implicit arguments.
 - *[partial]* Workers support.
 - *[inprogress]* Advanced Sentence splitting `(Parse (Sentence string))`, which can handle the whole document.

_Version 0.1_:

 - **[started]** Implement Locate -> "file name where the object is defined".
   To improve.

 - Redo Query API, make objects tagged with a GADT.
   *Critical: we hope to have gained enough experience to introduce the object tag*

 - Improve the handling of names and environments, see
   `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs

   Maybe we could add some options `Short`, `Full`, `Best` ? ...
   Or we could even serialize the naming structure and let the ide decide if we export the current open namespace.

 - Help with complex codepaths:

   Load Path parsing and completion code is probably one of the most complex part of company-coq

_Version 0.2_:

 - Support regexps in queries.

_More_:

 - Would be easy to get a list of vernacs? Things like `Print`, `Typeclasses eauto`, etc.

 - Checkstyle support.

 - Add a "document cache layer" where you can send a full document and Coq parses it in full and perform caching.

 - ppx to enumerate datatypes. Write the help command with this and also Clément suggestions about Vernac enumeration.

### Technical details

Coq SerAPI has two main components:

- `serialize` a library providing automatic de/serialization of most Coq data structures using ppx_conv_sexp. This should be eventually incorporated into Coq itself.
- `sertop`, a toplevel implementing an modified version of the current IDE protocol. This is a simple file and largely independent of Coq itself.

Building your own toplevels using `serialize` is encouraged. Here, the current limit is the Ml API itself.

#### Open Questions

- Should we fully embrace `Core` ?

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.

## Commit tag conventions [work in progress]:

- [misc]    : Code refactoring, miscellanenous
- [serlib]  : Serialization lib.
- [sertop]  : Toplevel.
- [doc]     : Documentation.
- [build]   : Build system.
- [proto]   : Core protocol.
- [control] : STM protocol.
- [query]   : Query protocol.
- [parse]   : Parsing protocol.
- [print]   : Printing protocol.

We prefer signed commits.

### Quick demo (not always up to date)

Using `rlwrap` or the emacs mode is highly recommended:

```lisp
coq-serapi$ rlwrap ./sertop.byte --prelude ~/external/coq-git/
(0 (Print () (CoqConstr (App (Rel 0) ((Rel 0))))))
> (Answer 0 Ack)
> (Answer 0(ObjList((CoqString"(_UNBOUND_REL_0 _UNBOUND_REL_0)"))))
(1 (Control (StmQuery 2 "Print nat. ")))
> (Answer 1 Ack)
> (Feedback((id(State 2))(contents Processed)(route 0)))
> (Feedback((id(State 0))(contents(Message ....))))
(2 (Print () (CoqRichpp (Element ....))))
> (Answer 2 Ack)
> (Answer 2(ObjList((CoqString"Inductive nat : Set :=  O : nat | S : nat -> nat\n\nFor S: Argument scope is [nat_scope]"))))
(3 (Control StmState))
> (Answer 3 Ack)
> (Answer 3(StmInfo 2))
(4 (Control (StmAdd 0 (Some 2) "Goal forall n, n + 0 = n.")))
> (Answer 4 Ack)
> (Answer 4(StmInfo 4))
(5 (Control (StmObserve 4)))
> (Answer 5 Ack)
> (Feedback((id(State 4))(contents(ProcessingIn master))(route 0)))
> ...
(Query ((pp ((pp_format PpStr)))) (Goals 4))
> (Answer 6 Ack)
> (Answer 6(ObjList((CoqString"forall n : nat, n + 0 = n"))))
(Query ((pp ((pp_format PpSexp)))) (Goals 4))
> (Answer 7 Ack)
> (Answer 7(ObjList((CoqGoal()(CProdN((fname"")....))))))
(8 (Control (StmAdd 0 (Some 4) "now induction n.")))
> (Answer 8 Ack)
> (Answer 8(StmInfo 5))
(10 (Control (StmObserve 5)))
> (Answer 10 Ack)
> (Feedback((id(State 5))(contents Processed)(route 0)))
> ...
(Query () (Goals 4))
> (Answer 11 Ack)
> (Answer 11(ObjList()))

```
