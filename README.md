## The Coq Se(xp)rialized Protocol

This repository provides a new communication protocol for the Coq theorem prover. It is based on automatic serialization of Ocaml datatypes from/to S-expressions, targeted to IDE and coding tools users.

SerAPI follows several design principles:

- Don't Repeat Yourself: SerAPI provides unique data structures and methods for each particular purpose. In this category fall query or printing commands. Different representations are automatically derived from the canonical ones.

- SerAPI tries to be extremely robust. It is liberal in what it accepts, and strict in what it produces.

- SerAPI tries to make the life of their consumers easier. If a particular use case is not well supported, we prefer adapting SerAPI than making users implement hacks.

- SerAPI tries to provide modular, reusable components. There is no reason some of its facilities couldn't be used by plugins, for instance.

SerAPI is a proof of concept and thus very unstable. It is meant to gather further feedback from coq IDE users and developers, the design is not final in way, comments are very welcome!

### Quick Overview and Documentation

After you run SerAPI (see [building](#building)) you should get a `sertop` binary, known as a _toplevel. The toplevel will read/write to stdin/stdout, so it is up to you to how to handle that. You can get an overview of SerAPI's options with `sertop -help`.

The base object in SerAPI is the `[CoqObject](sertop/sertop_protocol.mli#L22)`, a sum type encapsulating core Coq objects, automatically serialized.

**WARNING: Object packing will change in the future, however adapting should be straigforward**

There are four categories of commands:

- `(Control [sertop/sertop_protocol.mli#L66](control_cmd))`: Instruct Coq to perform some action. Typically to check a proof, set an option, modify a load_path, etc... Every type of call will produce a unique numeric tag for the command `(Answer id Ack)` and possibly zero or more different _tagged_ [answers](sertop/sertop_protocol.mli#52), to end with a tagged `(Answer id Completed)`.

- `(Query (preds limit pp) kind)`: **IMPORTANT: The Query API format will change soon, don't rely too much on it**
   Search for Coq objects of kind `kind`. This can range from options, current goals and hypotheses, tactics, etc... `preds` is a list of conjunctive filters and `limit` is an option type specifying how many values the query should return. `pp` controls the output format, with current value `PpSexp` for full serialization, `PpStr` for pretty printing. For instance:
   ```lisp
(Query (((Prefix "Debug")) (Some 10) PpSexp) Option)
   ```
   will query all Coq options that start with "Debug", limiting to the first 10 and printing the full internal Coq datatype:
   ```lisp
   (CoqOption (Default Goal Selector)
      ((opt_sync true) (opt_depr false) (opt_name "default goal selector")
      (opt_value (StringValue 1))))
   ```

- `(Print opts obj)`: The `Print` command provides access to the Coq printers. Thus, it is possible to manipulate the objects returned by `Query` and then have Coq print them.

- `(Parse opts obj)`: The `Parse` command gives access to IDEs to the Coq parsing engine.

Look into the [interface file](sertop/sertop_protocol.mli) for more details about the protocol itself. Ocaml type definitions are serialized in a straightforward manner so it should be easy to figure it out.

### Building

The build system is work in progress, as we would like to incorporate some changes to Coq upstream first. OPAM and coq are required.

1. Install the needed packages:
   `$ opam install ocamlfind ppx_import core_kernel sexplib ppx_sexp_conv`

2. Download and compile coq-trunk. In the coq sources you can do:
   `$ ./configure -local && make -j $NJOBS

3. Edit our `myocamlbuild.ml` to add the location of Coq sources and Opam installation, then
   `make`
   should do the rest.


### Emacs mode

Open `sertop.el` and run `M-x eval-buffer` followed by `M-x sertop` to get a sertop REPL in Emacs, with highlighting and pretty-printing (useful for debugging).

### Quick demo

Using `rlwrap` is highly recommended:

```lisp
coq-serapi$ rlwrap ./sertop.byte -prelude /home/egallego/external/coq-git/
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

### Roadmap/Changelog:

_Version 0.02_:

 - **[done]** Serialization of the `Proof.proof` object.
 - **[done]** Improve API: add options.
 - **[done]** Improve and review printing workflow.
 - **[done]** `(Query ((Prefix "add") (Limit 10) (PpStr)) $ObjectType)`
 - **[done]** Basic Sentence splitting `(Parse string))`, retuns the loc of the end of the sentence.
 - **[done]** Basic completion-oriented Search support `(Query () Names)`
 - **[partial]** Print Grammar tactic. `(Query ... (Tactics))`.
   Still we need to decide on
 - Implement Locate -> "file name where the object is defined".
   `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs
 - Better command line parsing (`Cmdliner`, `Core` ?)

_Version 0.03_:

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

 - Implicits.

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

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.
