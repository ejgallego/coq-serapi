## The Coq Se(xp)rialized Protocol

[![Build Status](https://travis-ci.org/ejgallego/coq-serapi.svg?branch=v8.7)](https://travis-ci.org/ejgallego/coq-serapi) [![Gitter](https://badges.gitter.im/coq-serapi/Lobby.svg)](https://gitter.im/coq-serapi/Lobby)

```
$ opam install coq-serapi
$ sertop --help
```

SerAPI is a library for machine-to-machine interaction with the Coq
proof assistant, with particular emphasis on IDE support and code
analysis tools. SerAPI provides automatic serialization of Ocaml
datatypes from/to S-expressions.

SerAPI is a proof-of-concept and should be considered
alpha-quality. However, it is fully functional and it supports
asynchronous proof checking, full-document parsing, and serialization
of Coq's core datatypes, among other things. SerAPI can also be run as
an in-browser thread, with typical load times less than a second.

The main design philosophy of SerAPI is to **make clients life easy**,
thus it tries to provide a convenient, robust interface that hides
away some of the most scary details involved in interaction with Coq.

As such, feedback from Coq users and developers is not only very
welcome, but _essential_ to the project. We are open to implementing new
features and exploring new use cases, let us know what you think via
the mailing list or in the issue tracker.

### Mailing List ###

SerApi development is discussed in the jsCoq mailing list, you can subscribe at:
https://x80.org/cgi-bin/mailman/listinfo/jscoq

The list archives should be also available at the Gmane group:
`gmane.science.mathematics.logic.coq.jscoq`. You can post to the list
using nntp.

### Roadmap

SerAPI 0.1 targets Coq 8.8. Current work is focused to improve Coq's
upstream API, in particular, the handling of proof documents. Once we
are happy with the document building and interaction API, work will
continue towards providing a rich, extensible query language.

### Quick Overview and Documentation

SerAPI for Coq is available as the OPAM package `coq-serapi`. See
[build instructions](notes/build.md) for instructions about manual
installation.

The main entry point to SerAPI is the `sertop` REPL, a basic toplevel
that reads and writes commands (S-Expressions) from stdin to stdout,
in a machine or human-friendly format. See `sertop --help` for
an overview of the main options. `Ctrl-C` will interrupt a busy Coq
process in the same way the standard `coqtop` does.

We recommend using `rlwrap` or the [emacs mode](sertop.el) for direct
interaction.

### Advanced / Developer use

With a bit more development effort, you can also:

- Use SerAPI as an Ocaml library. The low-level serialization library
  [`serlib/`](/serlib) and the higher-level SerAPI protocol in
  [`serapi/serapi_protocol.mli`](/serapi/serapi_protocol.mli) can be
  linked standalone.

- Use SerAPI web worker [JavaScript Worker](https://developer.mozilla.org/en-US/docs/Web/API/Web_Workers_API/Using_web_workers)
  from your web/node application. In this model, you communicate with SerAPI using
  the typical `onmessage/postMessage` worker API. Ready-to-use builds
  may be found at
  [here](https://github.com/ejgallego/jscoq-builds/tree/serapi), we
  provide an example REPL at: https://x80.org/rhino-hawk

- We would also like to provide a [Jupyter/IPython kernel](issues/17).

## Protocol Description

**API WARNING:** _The protocol is experimental and may change often_.

Up-to-date documentation for the protocol is in the [interface
file](serapi/serapi_protocol.mli). Given that serialization is
automatic, the Ocaml type definitions constitute the canonical
reference for the protocol.

### Coq Objects

SerAPI's main building block is the
[`CoqObject`](serapi/serapi_protocol.mli#L22) data type, a _sum type_
encapsulating most core Coq objects.

### Commands
Interaction with `sertop` is done using _commands_, which can be optionally tagged in the form of `(tag cmd)`; otherwise, an automatic tag will be assigned.
For every command, SerAPI **will always** reply with `(Answer tag Ack)` to indicate that the command was successfully parsed and delivered to Coq, or with a `SexpError` if parsing failed.

There are three categories of [commands](serapi/serapi_protocol.mli#L147):

- **Document manipulation:** `Add`, `Cancel`, `Exec`, ...: these commands instruct Coq to perform some action on the current document.
  Every command will produce zero or more different _tagged_ [answers](serapi/serapi_protocol.mli#52), and  a final answer `(Answer tag Completed)`, indicating that there won't be more output.

  SerAPI document commands are an evolution of the OCaml STM API, [here](https://github.com/ejgallego/jscoq/blob/master/etc/notes/coq-notes.md) and [here](https://github.com/siegebell/vscoq/blob/master/CoqProtocol.md) you can find a few informal notes on how it works. We are working on a more detailed specification, for now you can get some more details in the issue tracker.

- **Queries:** `(Query ((opt value) ...) kind)`:

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

- **Printing:** `(Print opts obj)`: The `Print` command provides access to the Coq pretty printers. Its intended use is for printing (maybe IDE manipulated) objects returned by `Query`.

### Quick demo (not always up to date)

Using `rlwrap` or the emacs mode is highly recommended:

```lisp
$ rlwrap ./sertop.byte --prelude ~/external/coq-git/
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

### Technical Report

There is a brief technical report with some details at
https://hal-mines-paristech.archives-ouvertes.fr/hal-01384408

## Acknowledgments

SerAPI has been developed at the
[Centre de Recherche en Informatique](https://www.cri.ensmp.fr/") of
[MINES ParisTech](http://www.mines-paristech.fr/) (former École de
Mines de Paris) and partially supported by the
[FEEVER](http://www.feever.fr) project.

## Clients using SerAPI

- [jsCoq](https://github.com/ejgallego/jscoq) allows you run Coq in
  your browser. JsCoq is the predecessor of SerAPI and will be shortly
  fully based on it. Meanwhile, you can access some of the technology
  from our sister project.

- [elcoq](https://github.com/cpitclaudel/elcoq), an emacs technology
  demo based on SerAPI by Clément Pit--Claudel. It is not fully
  functional but already illustrates some cool features.

- [peacoq][https://github.com/Ptival/PeaCoq] has a branch using SerAPI.

## Developer information

### Technical details

Coq SerAPI has three main components:

- `serapi`: an extended version of the current IDE protocol.
- `serlib` a library providing automatic de/serialization of most Coq data structures using `ppx_conv_sexp`. This should be eventually incorporated into Coq itself. Support for `ppx_deriving_yojson` is work in progress.
- `sertop`, `sertop_js`, toplevels offering implementation of the protocol.

Building your own toplevels using `serlib` and `serapi` is encouraged.

### Commit tag conventions [work in progress]:

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

