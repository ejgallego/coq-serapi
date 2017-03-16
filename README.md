## The Coq Se(xp)rialized Protocol

[![Build Status](https://travis-ci.org/ejgallego/coq-serapi.svg?branch=master)](https://travis-ci.org/ejgallego/coq-serapi)

SerAPI is a new library and communication protocol for the Coq proof
assistant. It is based on automatic serialization of Ocaml datatypes
from/to S-expressions; we aim to make low-level interaction with Coq
easier, putting particular emphasis on IDE/tool developers. However,
we believe that everybody can have some fun playing with our tool!

SerAPI currently provides two frontends to Coq: a standard "Coq
toplevel", **sertop**, and a JavaScript asynchronous version, allowing
to use SerAPI directly from your browser. We are working on a
Jupyter/IPython kernel.

The main design principles of SerAPI are:

- **Don't Repeat Yourself**: We build on top of Coq's plugin API, we have canonical commands (search, print).
- **Be extremely robust**: Any crash is a **critical** bug; we are liberal in what we accept, and strict in what we produce.
- **Make life easy**: We are flexible with abstractions in order to provide a user-oriented interface.

SerAPI is still a proof-of-concept. However, it already supports async
processing, most of the functionality available in Coq's XML protocol
plus a few extra things, and runs quite well in the browser. Typical
load times are less than a second.

Feedback from Coq users and developers is very welcome, contact us by
mail or in the issue tracker!

## Mailing List ##

SerApi development is discussed in the jsCoq mailing list, you can subscribe at:

https://x80.org/cgi-bin/mailman/listinfo/jscoq

The list archives should be also available at the Gmane group:

`gmane.science.mathematics.logic.coq.jscoq`

you can post to the list using nntp.

### Roadmap

We will provide a more detailed roadmap for developers soon, for now
you can find some sparse information below.

### Quick Overview and Documentation

SerAPI is meant to be a basis for developers to build Coq IDEs and
plugins.

If you are a Coq user, you have two choices:

- Use [jsCoq](https://github.com/ejgallego/jscoq) and run Coq in your
  browser. JsCoq is the predecessor of SerAPI and will be shortly
  fully based on it. Meanwhile, you can access the embedding
  technology from our sister project.
- [elcoq](https://github.com/cpitclaudel/elcoq), a first emacs IDE
  prototype using SerAPI by Clément Pit--Claudel. This is not yet
  functional but already very cool!

If you are a developer, you can use SerAPI in 3 different ways:

- As a
  [JavaScript Worker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
  from your web app. In this model, you communicate with SerAPI using
  the typical `onmessage/postMessage` worker API. Ready-to-use builds
  are typically found
  [here](https://github.com/ejgallego/jscoq-builds/tree/serapi), we
  provide an example REPL at:

  https://x80.org/rhino-hawk

- From your shell/application as a REPL: `sertop.native`.  The
  `sertop` toplevel reads and writes commands (S-Expressions) from
  stdin/stdout, in a machine or human-friendly format.  Asynchronous
  processing is supported, see `sertop.native --help` for an
  overview of the main options. `Ctrl-C` will interrupt a busy Coq
  process in the same way than the standard `coqtop` does.

  We recommend using `rlwrap` or our [emacs mode](sertop.el) for
  direct interaction.

- As an Ocaml library. You can directly link against the low-level
  serialization library `serlib/`, or against the higher-level SerAPI
  protocol in `sertop/sertop_protocol.mli`.

The installation process for the last two options is similar to a Coq
plugin, we hope to provide an OPAM package soon; for now, see the
[build instructions](#building).

#### Protocol

SerAPI's main building block is the [`CoqObject`](serapi/serapi_protocol.mli#L22) data type, a _sum type_ encapsulating most core Coq objects.

**API WARNING:** _Object packing will change in the future, however adapting should be straightforward_.

Interaction happens by means of _commands_, which can be optionally tagged in the form of `(tag cmd)`; otherwise, an automatic tag will be assigned.
For every command, SerAPI **will always** reply with `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are four categories of commands:

- `(Control `[`control_cmd`](serapi/serapi_protocol.mli#L73)`)`: control commands are similar to a function call and instruct Coq to perform some action.
  Typical actions are to check a proof, set an option, modify a `load path`, etc... Every command will produce zero or more different _tagged_ [answers](serapi/serapi_protocol.mli#52), and  a final answer `(Answer tag Completed)`, indicating that there won't be more output.

  We assume the reader familiar with Coq's STM, [here](https://github.com/ejgallego/jscoq/blob/master/etc/notes/coq-notes.md) and [here](https://github.com/siegebell/vscoq/blob/master/CoqProtocol.md) you can find a few informal notes on how it works, but we are documenting some of our extensions. See the issue tracker for more details.

- `(Query ((opt value) ...) kind)`:
  **API WARNING:** The Query API format is experimental and will change soon.

  Queries stream Coq objects of type `kind`. This can range from options, goals and hypotheses, tactics, etc... The first argument is a list of options: `preds` is a list of conjunctive filters, `limit` specifies how many values the query may return. `pp` controls the output format: `PpSer` for full serialization, or `PpStr` for "pretty printing". For instance:
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
  currently supported queries can be seen [here](serapi/serapi_protocol.mli#L118)

- `(Print opts obj)`: The `Print` command provides access to the Coq pretty printers. Its intended use is for printing (maybe IDE manipulated) objects returned by `Query`.

- `(Parse num string)`: The `Parse` command gives access to the Coq parsing engine. We currently support detecting the end of the first num sentences, returning the corresponding `CoqPosition` objects. If you want to parse a document use the `Add` control command instead.

Look at the [interface file](serapi/serapi_protocol.mli) more the details. The Ocaml type definitions are often self-explanatory and are serialized in a predictable way.

### Building

Building `sertop` requires OPAM and the development branch of [Coq 8.7](https://github.com/coq/coq/).

0. The current supported ocaml version is 4.04.0
   ``$ opam switch 4.04.0 && eval `opam config env` ``.
1. Install the needed packages:
   `$ opam install ocamlfind ocamlbuild ppx_import cmdliner core_kernel sexplib ppx_sexp_conv camlp5`.
2. Download and compile coq 8.7. We recommend:
   `$ ./configure -local && make -j $NJOBS`.
3. Edit the `SERAPI_COQ_HOME` variable in `Makefile` to add the location of
   your Coq sources. You can also override it with `make
   SERAPI_COQ_HOME=$path_to_coq`. Another alternative is to modify your
   `findlib.conf` to add the Coq path to findlib's search path.
4. Type `make` to build `sertop`.

### Emacs mode

Open `sertop.el` and run `M-x eval-buffer` followed by `M-x sertop` to get a sertop REPL in Emacs, with highlighting and pretty-printing (useful for debugging).

You may want to configure the variable `sertop-coq-directory` to point out the location of Coq's stdlib.

### Technical Report

There is a brief technical report at https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408

### Roadmap/Changelog:

See also the [CHANGELOG.md](CHANGELOG.md).

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

_More_:

 - Support regexps in queries.
 - Would be easy to get a list of vernacs? Things like `Print`, `Typeclasses eauto`, etc.
 - Add a cache to full document parsing..
 - enable an open CoqObject tag for plugin use (see coq/coq#209 ) ?
 - Checkstyle support.
 - ppx to enumerate datatypes. Write the help command with this and also Clément suggestions about Vernac enumeration.

### Technical details

Coq SerAPI has three main components:

- `serapi`: an extended version of the current IDE protocol.
- `serlib` a library providing automatic de/serialization of most Coq data structures using `ppx_conv_sexp`. This should be eventually incorporated into Coq itself. Support for `ppx_deriving_yojson` is work in progress.
- `sertop`, `sertop_js`, toplevels offering implementation of the protocol.

Building your own toplevels using `serlib` and `serapi` is encouraged. Here, the current limit is the ML API itself.

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.

## Commit tag conventions [work in progress]:

- [misc]    : Code refactoring, miscellanenous
- [serlib]  : Serialization lib.
- [sertop]  : Sexp Toplevel.
- [doc]     : Documentation.
- [build]   : Build system.
- [proto]   : Core protocol.
- [control] : STM protocol.
- [query]   : Query protocol.
- [parse]   : Parsing protocol.
- [print]   : Printing protocol.
- [js]      : Javascript version.

We prefer signed commits.

### Quick demo (not always up to date)

Using `rlwrap` or the emacs mode is highly recommended:

```lisp
coq-serapi$ rlwrap ./sertop.byte --prelude ~/external/coq-git/
(0 (Print () (CoqConstr (App (Rel 0) ((Rel 0))))))
> (Answer 0 Ack)
> (Answer 0(ObjList((CoqString"(_UNBOUND_REL_0 _UNBOUND_REL_0)"))))
(1 (Query () (Vernac "Print nat. ")))
> (Answer 1 Ack)
> (Feedback((id(State 2))(contents Processed)(route 0)))
> (Feedback((id(State 0))(contents(Message ....))))
(2 (Print () (CoqRichpp (Element ....))))
> (Answer 2 Ack)
> (Answer 2(ObjList((CoqString"Inductive nat : Set :=  O : nat | S : nat -> nat\n\nFor S: Argument scope is [nat_scope]"))))
(4 (Control (Add () "Goal forall n, n + 0 = n.")))
> (Answer 4 Ack)
> (Answer 4(Added 4 loc))
(5 (Control (Exec 4)))
> (Answer 5 Ack)
> (Feedback((id(State 4))(contents(ProcessingIn master))(route 0)))
> ...
(Query ((sid 4) (pp ((pp_format PpStr)))) Goals)
> (Answer 6 Ack)
> (Answer 6(ObjList((CoqString"forall n : nat, n + 0 = n"))))
(Query ((sid 4) (pp ((pp_format PpSer)))) Goals)
> (Answer 7 Ack)
> (Answer 7(ObjList((CoqGoal()(CProdN((fname"")....))))))
(8 (Control (Add () "now induction n.")))
> (Answer 8 Ack)
> (Answer 8(Added 5 loc))
(10 (Control (Exec 5)))
> (Answer 10 Ack)
> (Feedback((id(State 5))(contents Processed)(route 0)))
> ...
(Query ((sid 4)) Goals)
> (Answer 11 Ack)
> (Answer 11(ObjList()))

```
