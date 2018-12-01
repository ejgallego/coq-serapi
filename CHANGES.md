_Version 0.6.0_:

 * [general] support Coq 8.9,
 * [general] SerAPI now uses Dune as a build system,
 * [opam]   install `sertop.el`,
 * [serlib] support to serialize kernel environments,
 * [serapi] new query `Env` that tries to print the current kernel environment,
 * [serlib] correct field names for `CAst`,
 * [serlib] more robust support for opaque / non-serializable types (#61, #68).
            Thanks to @palmskog,
 * [serlib] new option `--exn_on_opaque` to raise an exception on
            non-serializable types; closes #68, thanks to @palmskog,
 * [serlib] serialization test-suite from
            https://github.com/proofengineering/serapi-tests, thanks to
            @palmskog,
 * [sercomp] add `--mode` option to better control output,
 * [sercomp] add `compser` for deserialization (inverse of `sercomp`)
             (@palmskog),
 * [serapi]  Allow custom document creation using the `NewDoc` call.
             Use the `--no_init` option to avoid automatic creation
             on init. (@ejgallego)
 * [sercomp] Allow compilers to output `.vo` (@ejgallego , suggested by
             @palmskog)
 * [sercomp] Serialize top-level vernaculars with their syntactic
             attributes (such as location) (@ejallego)

_Version 0.5.7_:

 * [serlib] Fixed serializers for more tactics data, add support for
   `ground` plugin (#68). Thanks again to @palmskog for the report.

_Version 0.5.6_:

 * [serlib] Fixed serializers for some tactics data (#66) Thanks to
   @palmskog for the report.

_Version 0.5.5_:

 * [serlib] Be more lenient when parsing back `Id.t` as to accommodate
   hacks in the Coq AST (#64) Thanks to @palmskog for the report.

_Version 0.5.4_:

 * [serlib] Fix critical bug in handling of abstract type (#60)

_Version 0.5.3_:

 * [sertop] Support for `-I` option (`--ml-include-path`).

_Version 0.5.2_:

 * [serlib] Compatibility with OCaml 4.07.0 [problems with `Stdlib` packing]

_Version 0.5.1_:

 * [serlib] (basic) support for serialization of the ssreflect grammar,
 * [serapi] `(Query () (Ast n))` is now `(Query ((sid n)) Ast)`,
 * [serapi] remove broken deprecated `SetOpt` and `LibAdd` commands,
 * [doc] Improved man page.
 * [js] Miscellaneous improvements on the js build.

_Version 0.5.0_:

 * [general] support Coq 8.8, use improved document API,
 * [sertop] By default `sertop` will create a new document with `doc_id` 0,
 * [sertop] new debug options, see `sertop --help`.

_Version 0.4_:

 * [general] support Coq 8.7 , make use of improved upstream API,
 * [sertop] support `-R` and `-Q` options, note the slightly different
   syntax wrt Coq upstream: `-R dir,path` in place of `-R dir path`,
 * [serlib] support serialization of generic arguments [#41],
 * [serapi] `(ReadFile file)`: hack to load a completed file.

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
