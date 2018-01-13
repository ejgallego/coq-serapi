## What is SerAPI?

Is a library plus a set of "toplevels" aimed to improve the
communication of third party tools with Coq.

## How mature is SerAPI?

SerAPI has _extremely experimental_ status, and there are no protocol
stability guarantees. In fact, the protocol is expected to evolve.

## Which Coq versions does SerAPI support?

At the moment, Coq 8.8 is the current supported version for the
current protocol. Older versions (8.6/8.7) should work however the
protocol will differ.

## How can I install SerAPI?

The supported way is to use the OPAM package manager. The
`.travis.yml` file contains up to date install instructions on how to
build it manually.

## Why does SerAPI hang with inputs larger than 4096 characters?

This is due to a historical limitation of the UNIX/Linux TTY API. See
#38. If you communicate with SerAPI using a PIPE this shouldn't be a
problem, otherwise you can use the `ReadFile` command in interactive mode.

## Can SerAPI produce `.vo` files?

Not yet, but support for this is planned.

## Does SerAPI support asyncronous proof proccessing?

It does, note however that it is still in experimental status
upstream. In particular there are some issues on Windows, and `EditAt`
may be inconvenient to use. We recommend not using `EditAt` and
instead using the less powerful `Cancel` for now.

## Does SerAPI support Coq's command line flags:

We don't support `coqtop` command line flags. SerAPI aims to be
"command line flag free", with all the options for each document
passed in the document creation call.

For 3rd party packages, SerAPI aims to adopt the package format
developed for jsCoq.

However, limited `_CoqProject` support is planned in order to
configure load paths. We will also support some legacy options `-R` in
order to make life bearable to some.

## What does SerAPI expose?

SerAPI exposes the core Coq datatypes. Tactics, AST, kernel terms and
types are all serialized. We also provide an API to manipulate and
query "Coq documents".

## How many ASTs does Coq have?

That's a very interesting question! The right answer is: _countably many_!

Logician jokes aside, the truth is that Coq features an extensible
AST. While this gives great power to plugins, it means that consumers
of the AST need to design their tools to support an _open_ AST.

Coq's basic parsing AST is called `vernac_expr`, which contain Coq
commands. Extensions happen under the `VernacExtend` constructor,
which contains a list of "generic arguments".

### Interpretation and Terms

Coq terms undergo 2 elaboration phases before reaching "kernel"
form. The top-level parsing type is named `constr_expr`, which will
then be _internalized_ to a `glob_constr`.

Type inference (called pretyping in Coq, as typing is usually reserved
for kernel-level type checking) will turn a `glob_constr` into a
full-typed `Constr.t` value, which is the core term type manipulated
by Coq's kernel and tactics.

When a _generic argument_ is added to Coq's AST, we must also provide
the corresponding interpretation and pretyping functions. To that
purpose, generic arguments have associated 3-levels, `raw`, `glb`, and
`top` which correspond to parsing-level, internalized-level, and
kernel-level.

Thus, a generic argument of type `foo`, may carry 3 different OCaml
types depending on the level the type is. This is used for example to
define the AST of _LTAC_ tactics, where the expression `pose s := foo`
with `foo` initially a `constr_expr` will undergo interpretation and
inference up to a term with a fully elaborated `foo` term.
