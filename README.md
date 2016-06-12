## The Coq Se(xp)rialized Protocol

This repository provides a new communication protocol for the Coq theorem prover. It is based on automatic serialization of Ocaml datatypes from/to S-expressions, targeted to IDE and coding tools users.

SerAPI follows several design principles:

- **Don't Repeat Yourself**: We have canonical data structures and methods for each particular purpose. There is a single query or printing command for all objects.
- **Be extremely robust**: We are liberal in what we accept, and strict in what we produce. Any crash is a **critical** bug.
- **Make life easy**: Provide a user-oriented interface.

SerAPI is an unstable proof of concept and the design is not final in any way.

At this stage, we'd like to gather feedback from coq IDE users and developers, comments are very welcome!

### Quick Overview and Documentation

We hope to provide SerAPI as an OPAM package soon; for now, see [building](#building).

SerAPI provides a `sertop.native` binary, known as a _Coq toplevel_. This toplevel reads and write commands from stdin/stdout, it is up to you how to best interface with it. We recommend the [emacs mode](sertop.el) or `rlwrap` for command line users. `sertop -help` will provide an overview of command line options.

SerAPI API's main building block is the [`CoqObject`](sertop/sertop_protocol.mli#L22) data type, a sum type encapsulating most core Coq objects, which can be automatically serialized. **API WARNING:** _Object packing will change in the future, however adapting should be straightforward_.

Interaction happens by means of _commands_, which are always tagged to distinguish responses, in the form of `(tag cmd)`. For every command, SerAPI **always** replies with an `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are four categories of commands:

- `(Control `[`control_cmd`](sertop/sertop_protocol.mli#L66)`)`: AKIN function calls, control commands instruct Coq to perform some action. Typical actions are to check a proof, set an option, modify a `load path`, etc... Every command will produce zero or more different _tagged_ [answers](sertop/sertop_protocol.mli#52), and will always finish with a `(Answer tag Completed)`.

   This part of the API assumes the reader is familiar with Coq's STM, [here](https://github.com/ejgallego/jscoq/blob/master/notes/coq-notes.md) you can find a few informal notes on how it works.

- `(Query (preds limit pp) kind)`: **API WARNING: The Query API format is experimental and will change soon, don't rely too much on it**
   Queries stream Coq objects of kind `kind`. This can range from options, goals and hypotheses, tactics, etc... `preds` is a list of conjunctive filters and `limit` is an option type specifying how many values the query should return. `pp` controls the output format, with current values `PpSexp` for full serialization, and `PpStr` for pretty printing. For instance:
   ```lisp
   (tag (Query (((Prefix "Debug")) (Some 10) PpSexp) Option))
   ```
   will stream all Coq options that start with "Debug", limiting to the first 10 and printing the full internal Coq datatype:
   ```lisp
   (CoqOption (Default Goal Selector)
      ((opt_sync true) (opt_depr false) (opt_name "default goal selector")
      (opt_value (StringValue 1))))
   ...
   ```

   Currently supported queries can be seen [here](sertop/sertop_protocol.mli#L110)

- `(Print opts obj)`: The `Print` command provides access to the Coq pretty printers. Its intended use is for printing manipulated objects returned by `Query`.

- `(Parse num string)`: The `Parse` command gives access to the Coq parsing engine. We currently support detecting the end of the first num sentences, returning the corresponding `CoqPosition` objects. Note that we don't execute the commands themselves so stateful parsing doesn't work.

Look at the [interface file](sertop/sertop_protocol.mli) for all the details. Ocaml type definitions are serialized in a straightforward manner so it should be easy to figure the syntax out.

### Building

The build system is work in progress. coq/coq#187 needs to be completed before we can put SerAPI in Opam.

To build, OPAM and coq are required.

1. Install the needed packages:
   `$ opam install ocamlfind ppx_import cmdliner core_kernel sexplib ppx_sexp_conv`

2. Download and compile coq-trunk. In the coq sources you can do:
   `$ ./configure -local && make -j $NJOBS`

3. Edit our `myocamlbuild.ml` to add the location of Coq sources and Opam installation, then
   `make` should do the rest.

### Emacs mode

Open `sertop.el` and run `M-x eval-buffer` followed by `M-x sertop` to get a sertop REPL in Emacs, with highlighting and pretty-printing (useful for debugging).

You may want to configure the variable `sertop-coq-directory` to point out the location of Coq's stdlib.

### Quick demo

Using `rlwrap` is highly recommended:

```lisp
coq-serapi$ rlwrap ./sertop.byte -prelude /home/egallego/external/coq-git/
(0 (Print (CoqConstr (App (Rel 0) ((Rel 0))))))
> (Answer 0 Ack)
> (Answer 0(ObjList((CoqString"(_UNBOUND_REL_0 _UNBOUND_REL_0)"))))
(1 (Control (StmQuery 2 "Print nat. ")))
> (Answer 1 Ack)
> (Feedback((id(State 2))(contents Processed)(route 0)))
> (Feedback((id(State 0))(contents(Message ....))))
(2 (Print (CoqRichpp (Element ....))))
> (Answer 2 Ack)
> (Answer 2(ObjList((CoqString"Inductive nat : Set :=  O : nat | S : nat -> nat\n\nFor S: Argument scope is [nat_scope]"))))
(3 (Control StmState))
> (Answer 3 Ack)
> (Answer 3(StmInfo 2))
(4 (Control (StmAdd 2 "Goal forall n, n + 0 = n.")))
> (Answer 4 Ack)
> (Answer 4(StmInfo 4))
(5 (Control (StmObserve 4)))
> (Answer 5 Ack)
> (Feedback((id(State 4))(contents(ProcessingIn master))(route 0)))
> ...
(6 (Query (None PpStr) Goals))
> (Answer 6 Ack)
> (Answer 6(ObjList((CoqString"forall n : nat, n + 0 = n"))))
(7 (Query (None PpSexp) Goals))
> (Answer 7 Ack)
> (Answer 7(ObjList((CoqGoal()(CProdN((fname"")....))))))
(8 (Control (StmAdd 4 "now induction n.")))
> (Answer 8 Ack)
> (Answer 8(StmInfo 5))
(10 (Control (StmObserve 5)))
> (Answer 10 Ack)
> (Feedback((id(State 5))(contents Processed)(route 0)))
> ...
(11 (Query (None PpStr) Goals))
> (Answer 11 Ack)
> (Answer 11(ObjList()))

```

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

 - **[started]** Implicit arguments.
 - **[started]** Implement Locate -> "file name where the object is defined".
   To improve.

 - Implement Locate -> "file name where the object is defined".

 - Workers support.
 - *[inprogress]* Port CoqIDE to SerAPI. See preliminary tree at https://github.com/ejgallego/coqide-exp/tree/serapi/

_Version 0.04_:

 - Redo Query API, make objects tagged with a GADT.
   *Critical: we hope to have gained enough experience to introduce the object tag*

 - Improve the handling of names and environments, see
   `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs

   Maybe we could add some options `Short`, `Full`, `Best` ? ...
   Or we could even serialize the naming structure and let the ide decide if we export the current open namespace.

 - Advanced Sentence splitting `(Parse (Sentence string))`, which can handle the whole document.

 - Help with complex codepaths:
   Load Path parsing and completion code is probably one of the most complex part of company-coq

_Version 0.04_:

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
- What should we adopt as document model?

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.

## Commit tag conventions [work in progress]:

- [serlib] : Serialization lib.
- [sertop] : Toplevel.

- [doc]   : Documentation.
- [build] : Build system.

- [proto]   : Core protocol.
- [control] : STM protocol.
- [query]   : Query protocol.
- [parse]   : Parsing protocol.
- [print]   : Printing protocol.
