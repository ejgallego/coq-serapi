## What is SerAPI?

Is a library plus a set of "toplevels" aimed to improve the
communication of third party tools with Coq.

## How mature is SerAPI?

SerAPI has _extremely experimental_ status, and there are no protocol
stability guarantees. In fact, the protocol is expected to evolve.

## Which Coq versions does SerAPI support?

At the moment, Coq 8.7 is the current supported version for the
current protocol. Older versions (8.6) should work however the
protocol will differ.

## How can I install SerAPI?

The supported way is to use OPAM. The `.travis.yml` file contains up
to date install instructions for each branch.

## Why does SerAPI hang with inputs larger than 4096 characters?

This is due to a historical limitation of the UNIX/Linux TTY API. See
#38. You can use

## Can SerAPI produce `.vo` files?

Not yet, but support for this is planned.

## Does SerAPI support asyncronous proof proccessing?

It does, note however that it is still in experimental status upstream. In particular

## Does SerAPI support Coq's command line flags:

We don't support `coqtop` command line flags. SerAPI aims to be
"command line flag free", with all the options for each document
passed in the document creation call.

For 3rd party packages, SerAPI aims to adopt the package format
developed for jsCoq.

However, limited `_CoqProject` support is planned in order to
configure load paths.

