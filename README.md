## The Coq Se(xp)rialized Protocol

[![Build Status](https://travis-ci.org/ejgallego/coq-serapi.svg?branch=master)](https://travis-ci.org/ejgallego/coq-serapi) [![Gitter](https://badges.gitter.im/coq-serapi/Lobby.svg)](https://gitter.im/coq-serapi/Lobby)

SerAPI is a library for machine-to-machine interaction with the Coq
proof assistant, with particular emphasis on helping writing IDEs and
code analysis tools. However, we believe that everybody can have some
fun playing with our tool!

SerAPI is based on the automatic serialization of Ocaml datatypes
from/to S-expressions. We currently provide two frontends: a
command-line based "Coq toplevel", **sertop**, and a JavaScript
[Worker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers),
which allows to use SerAPI directly from your browser. There is also
plans to provide a Jupyter/IPython kernel (#17).

SerAPI is still a proof-of-concept and in heavy development, but it
already supports asynchronous processing, most of the functionality
available in Coq's XML protocol, and some basic queries. Typical load
times in the browser are less than a second.

SerAPI is a user-oriented tool, thus our main design philosophy is
**make life easy** to the clients, by providing convenient, robust
APIs and polishing out the most scary details of interaction with Coq.
Feedback from Coq users and developers is not only very welcome, but
essential to the project. Let us know what you think via the mailing
list or in the issue tracker.

## Mailing List ##

SerApi development is discussed in the jsCoq mailing list, you can subscribe at:

https://x80.org/cgi-bin/mailman/listinfo/jscoq

The list archives should be also available at the Gmane group:

`gmane.science.mathematics.logic.coq.jscoq`

you can post to the list using nntp.

### Roadmap

SerAPI 0.1 targets Coq 8.7. We are focused on incorporating some
crucial changes in to Coq upstream to improve handling of
documents. Our first goal is to get a robust document building and
interaction API, then we will focus on providing a rich, extensible
query language.

### Quick Overview and Documentation

If you are a Coq user, you can use:

- [jsCoq](https://github.com/ejgallego/jscoq) allows you run Coq in
  your browser. JsCoq is the predecessor of SerAPI and will be shortly
  fully based on it. Meanwhile, you can access some of the technology
  from our sister project.
- [elcoq](https://github.com/cpitclaudel/elcoq), an emacs technology
  demo based on SerAPI by Clément Pit--Claudel. It is not fully
  functional but already illustrates some cool features.

If you are a developer, you can use SerAPI in 3 different ways:

- As a
  [JavaScript Worker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
  from your web/node application. In this model, you communicate with SerAPI using
  the typical `onmessage/postMessage` worker API. Ready-to-use builds
  are typically found
  [here](https://github.com/ejgallego/jscoq-builds/tree/serapi), we
  provide an example REPL at:

  https://x80.org/rhino-hawk

- From your shell/application as a REPL: `sertop` is a basic toplevel
  that reads and writes commands (S-Expressions) from stdin to stdout,
  in a machine or human-friendly format.  Asynchronous processing is
  supported. See `sertop.native --help` for an overview of the main
  options. `Ctrl-C` will interrupt a busy Coq process in the same way
  than in the standard `coqtop`.

  We recommend using `rlwrap` or our [emacs mode](sertop.el) for
  direct interaction.

- As an Ocaml library. You can directly link against the low-level
  serialization library [`serlib/`](/serlib), or against the higher-level SerAPI
  protocol in [`serapi/serapi_protocol.mli`](/serapi/serapi_protocol.mli).

See [build instructions](#building) but information about
installation. We will provide an OPAM real soon now.

#### Protocol

Up-to-date documentation for the protocol is in the
[interface file](serapi/serapi_protocol.mli). The Ocaml type
definitions are often self-explanatory and are serialized in a
predictable way.

SerAPI's main building block is the
[`CoqObject`](serapi/serapi_protocol.mli#L22) data type, a _sum type_
encapsulating most core Coq objects.

**API WARNING:** _Object packing will change in the future, however adapting should be straightforward_.

Interaction happens by means of _commands_, which can be optionally tagged in the form of `(tag cmd)`; otherwise, an automatic tag will be assigned.
For every command, SerAPI **will always** reply with `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are four categories of [commands](serapi/serapi_protocol.mli#L147):

- `Add`, `Cancel`, `Exec`, ...: these commands instruct Coq to perform some action on the current document.
  Every command will produce zero or more different _tagged_ [answers](serapi/serapi_protocol.mli#52), and  a final answer `(Answer tag Completed)`, indicating that there won't be more output.

  SerAPI document commands are an evolution of the OCaml STM API, [here](https://github.com/ejgallego/jscoq/blob/master/etc/notes/coq-notes.md) and [here](https://github.com/siegebell/vscoq/blob/master/CoqProtocol.md) you can find a few informal notes on how it works. We are on a more detailed specification, for now you can get some more details in the issue tracker.

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

### Building

`sertop` is available for different Coq versions, which each of its
branches targetting the corresponding Coq branch. The current
development branch is `v8.7`, for Coq v8.7. The `master` branch is
currently broken and won't be resurrected until Coq 8.8 is closer to
release.

Basic build instructions are below, we recommend having look at the
`.travis.yml` files to see more details on how a particular branch is
built.

We recommend using OPAM to build `sertop`, however Théo Zimmermann has
also reported success in NixOS.

0. The currently supported ocaml version is 4.04.2
   ``$ opam switch 4.04.2 && eval `opam config env` ``. We also assume `COQVER=v8.7`.
1. Install the needed packages:
   `$ opam install ocamlfind ocamlbuild ppx_import ppx_deriving=4.1 cmdliner core_kernel sexplib ppx_sexp_conv camlp5`.
   As of today, there are some _hard_ version dependencies: `ppx_sexp_conv >=
   v0.9.0` and `ppx_deriving=4.1`. See `.travis.yml` for more details.
2. Download and compile coq. We recommend:
   `$ git clone -b ${COQVER} https://github.com/coq/coq.git ~/external/coq-${COQVER} && cd ~/external/coq-${COQVER} && ./configure -local -native-compiler no && make -j $NJOBS`.
3. Type `make SERAPI_COQ_HOME=~/external/coq-${COQVER}` to build `sertop`.

The above instructions assume that you use `~/external/coq-${COQVER}`
directory to place the coq build that SerAPI needs; you can modify
the `SERAPI_COQ_HOME` variable in `Makefile` to make this change
permanent, or override the provided default.

Another alternative is to modify your `findlib.conf` file to add Coq's
path to findlib's search path: for example, edit the file `~/.opam/4.04.2/lib/findlib.conf` and change
`path="/home/egallego/.opam/4.04.2/lib"` by `path="/home/egallego/.opam/4.04.2/lib:/home/egallego/external/coq-v8.7"`.

This is convenient to use `merlin`. If you install Coq globally, these
steps may not be needed, findlib may be able to locate Coq for you;
YMMV.

### Emacs mode

Open `sertop.el` and run `M-x eval-buffer` followed by `M-x sertop` to get a sertop REPL in Emacs, with highlighting and pretty-printing (useful for debugging).

You may want to configure the variable `sertop-coq-directory` to point out the location of Coq's stdlib.

### Technical Report

There is a brief technical report with some details at
https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408

### Roadmap/Changelog:

See also the [CHANGELOG.md](CHANGELOG.md).

_Version 0.1_:

 - Full document parsing. Full asynchronous `Add/Cancel` protocol.

 - **[started]** Implement Locate -> "file name where the object is defined".
   To improve.

 - Improve the handling of names and environments, see
   `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs

   Maybe we could add some options `Short`, `Full`, `Best` ? ...
   Or we could even serialize the naming structure and let the ide decide if we export the current open namespace.

 - Help with complex codepaths:
   Load Path parsing and completion code is probably one of the most complex part of company-coq

_Version 0.2_:

 - Redo Query API, make objects tagged with a GADT.
   *Critical: we hope to have gained enough experience to introduce the object tag*

_More_:

 - Support regexps in queries.
 - Would be easy to get a list of vernacs? Things like `Print`, `Typeclasses eauto`, etc.
 - ppx to enumerate datatypes. Write the help command with this and also Clément suggestions about Vernac enumeration.
 - Add a cache to full document parsing..
 - enable an open CoqObject tag for plugin use (see coq/coq#209 ) ?
 - Checkstyle support.

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
(4 (Add () "Goal forall n, n + 0 = n."))
> (Answer 4 Ack)
> (Answer 4(Added 4 loc))
(5 (Exec 4))
> (Answer 5 Ack)
> (Feedback((id(State 4))(contents(ProcessingIn master))(route 0)))
> ...
(Query ((sid 4) (pp ((pp_format PpStr)))) Goals)
> (Answer 6 Ack)
> (Answer 6(ObjList((CoqString"forall n : nat, n + 0 = n"))))
(Query ((sid 4) (pp ((pp_format PpSer)))) Goals)
> (Answer 7 Ack)
> (Answer 7(ObjList((CoqGoal()(CProdN((fname"")....))))))
(8 (Add () "now induction n."))
> (Answer 8 Ack)
> (Answer 8(Added 5 loc))
(10 (Exec 5))
> (Answer 10 Ack)
> (Feedback((id(State 5))(contents Processed)(route 0)))
> ...
(Query ((sid 4)) Goals)
> (Answer 11 Ack)
> (Answer 11(ObjList()))

```
