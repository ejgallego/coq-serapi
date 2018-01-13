_Version 0.5_:

 * support Coq 8.8 , make use of improved upstream API,
 * `(Query () (Ast n))` is now `(Query ((sid n)) Ast)`

_Version 0.4_:

 * support `-R` and `-Q` options, note the slightly different syntax
   wrt Coq upstream: `-R dir,path` in place of `-R dir path`
 * support Coq 8.7 , make use of improved upstream API,
 * support serialization of generic arguments [#41],
 * full file support hack

_Version 0.2_:

 * Better Query/Object system.

_Version 0.1_:

 * Serialization-independent protocol core,
 * [js] Javascript worker,
 * [lib] Better Prelude support,
 * [serlib] Full Serialization of generic arguments,
 * [proto] Add is not a synchronous call anymore,
 * [proto] Refactor into a flat command hierarchy,
 * [proto] More useful queries,
 * [proto] Guarantee initial state is 1,
 * [proto] Support for ltac profiling,
 * [proto] Printing: add depth limiting,
 * [proto] Better handling of options in the sexp backend.

_Version 0.03_:

 * **[done]** Implicit arguments.
 * **[done]** Coq Workers support.
 * **[done]** Advanced Sentence splitting `(Parse (Sentence string))`, which can handle the whole document.

_Version 0.02_:

 * **[done]** Serialization of the `Proof.proof` object.
 * **[done]** Improve API: add options.
 * **[done]** Improve and review printing workflow.
 * **[done]** `(Query ((Prefix "add") (Limit 10) (PpStr)) $ObjectType)`
 * **[done]** Basic Sentence splitting `(Parse num string))`, retuns the first num end of the sentences _without_ executing them.
              This has pitfalls as parsing is very stateful.
 * **[done]** Basic completion-oriented Search support `(Query () Names)`
 * **[done]** Better command line parsing (`Cmdliner`, `Core` ?)
 * **[partial]** Print Grammar tactic. `(Query ... (Tactics))`.
   Still we need to decide on:
   `Coq.Init.Notations.instantiate` vs `instantiate`, the issue of
   `Nametab.shortest_qualid_of_global` is a very sensible one for IDEs
