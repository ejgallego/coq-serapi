## Version 0.18.2:

 - [serlib] Expose some more Ast functions required by coq-lsp's
            auto-build support (@ejgallego, #383)

## Version 0.18.1:

 - [serlib] Fix a few 8.18 piercings (!) (@ejgallego, #357)

## Version 0.18.0:

 - [serapi] (!) support for Coq 8.18, thanks to all the developers
            that contributed compatibility patches (@ejgallego and
            many others).
 - [serlib] Fix ltac2 plugin wrong piercing due to missing constructor
            (@ejgallego, reported by @quarkcool, #349).

## Version 0.17.2:

 - [serlib] Expose some more Ast functions required by coq-lsp's
            auto-build support (@ejgallego, #383)

## Version 0.17.1:

 - [sertop] Don't initialize `CoqworkmgrApi` (@ejgallego, #340)
 - [serlib] Compat with Jane Street libraries >= v0.16.0 (@ejgallego,
            #351)

## Version 0.17.0:

 - [serlib] (!) Serialization format of generic arguments has changed
            to be conforming to usual `ppx_sexp_conv` conventions.
            (@ejgallego , fixes #273)
 - [serapi] (!) support for Coq 8.17, upstream structures seem pretty
            stable from 8.16, except for `Constr.Evar` (@ejgallego)
 - [serapi] SerAPI is now in Coq's CI (@ejgallego @alizter)

## Version 0.16.3:

 - [serlib] Fix JSON serialization for generic arguments (@ejgallego, #321)

## Version 0.16.2:

 - [sertop] Add `--impredicative-set` command line option (@dhilst , #288)
 - [serlib] Added support for some more plugins from coq-core (ltac2,
            cc, micromega, number_string_notation) (@ejgallego, #284, #306)

## Version 0.16.1:

 - [sertop] Allow to set `--coqlib` using the `COQLIB` environment
            variable. The cmdline argument option still has
            precedence.
 - [serapi] Allow to parse expressions too with
            `(Parse (entry Constr) $text)` (@ejgallego, fixes #272)

## Version 0.16.0:

 - [serapi] (!) support for Coq 8.16, see upstream changes and SerAPI
            test-suite changes for more information. Remarkable
            changes are:
            - kernel terms are serialized a bit differently now due to
              KerName being used in more places upstream. Some
              internal structures also changes in kernel's env, so be
              attentive if you are depending on them.
            - plugin loading is adapted for 8.16 findlib loading
              method
            (@ejgallego)
 - [deps]   Require cmdliner >= 1.1.0 (@ejgallego)
 - [deps]   Support Jane Street libraries v0.15.0 (@ejgallego)
 - [serapi] New query `Objects` to dump Coq's libobject (@ejgallego)
 - [serlib] Much improved yojson / json support (@ejgallego)
 - [serlib] Coq AST now supports ppx_hash intf (ignoring locations by default)
            (@ejgallego)
 - [serlib] Coq AST now supports ppx_compare intf (ignoring locations by default)
            (@ejgallego)
 - [serlib] Large refactoring on Serlib, using functors, see serlib/README.md
            (@ejgallego)
 - [serapi] (!) Query `Proofs` has changed type and will now return the
            partial terms under construction (#271 , fixes #270, @ejgallego)

## Version 0.15.1:

 - [serlib] Fix bad bypass of opaquetab serialization. This caused a
            segfault in some cases.

## Version 0.15.0:

 - [serapi] (!) support for Coq 8.15, see upstream changes; nothing
            too remarkable so far, except for `NewTip` -> `NewAddTip`
            in the answer response, we may want to add a compat layer
            for this if problematic. (#265, @ejgallego)

## Version 0.14.0:

 - [serapi] (!) support for Coq 8.14, see upstream changes; nothing
            too remarkable other than `NewDoc` will now ignore
            loadpaths due to new init setup upstream.
            (#253, @ejgallego)
 - [ci]     SerAPI branches should be able to build now against Coq rc
            packages as to better integrate with Coq's platform beta
            release; thanks to Érik Martin-Dorel, Karl Palmskog and Théo
            Zimmermann for feedback.

## Version 0.13.1:

 - [serapi] New query `(Query () (LogicalPath file))` which will
            return the logical path for a particular `.v` file
            (@ejgallego, see also
            https://github.com/cpitclaudel/alectryon/pull/25)
 - [serapi] new `(SaveDoc opts)` command supporting saving of .vo
            files even when from interactive mode; note that using
            `--topfile` is required (fixes #238, @ejgallego, reported
            by Jason Gross)
 - [sertop] we don't link the OCaml `num` library anymore, this could
            have some impact on plugins (@ejgallego)
 - [nix]    Added Nix support (#249, fixes #248, @Zimmi48, reported
            by @nyraghu)
 - [serapi] Fix COQPATH support: interpret paths as absolute (#249, @Zimmi48)
 - [serlib] Ignore `env` parameter in certain exceptions (#254, fixes #250,
            @ejgallego, reported by @cpitclaudel)
 - [sertop] New option `--omit_env` that will disable the serialization of
            Coq's super heavy global environments (#254 @ejgallego)
 - [build]  Test OCaml 4.12 (#257 @ejgallego)
 - [sertop] Async mode was not working due to passing `-no-glob` to workers

## Version 0.13.0:

 - [serapi] (!) support for Coq 8.13, see upstream changes; in
            particular there are changes in the kernel representation
            of terms [pattern matching, new caseinvert, primitive arrays]
            (#232, fixes #227, @ejgallego)

## Version 0.12.1:

 * [serapi]  (!) Bump public library versioning [breaking change]
 * [opam]    Bump upper bound on ppx_sexp_conv to 0.15, allowing SerAPI
             to work with the 0.14 set of Jane Street packages.
 * [serapi]  Fix goal printing anomaly (#230, fixes #228 @corwin-of-amber)
 * [sertop ] New `(Fork (fifo_in file) (fifo_out file))` command, that
             will (hard) fork a new SerAPI process and redirect the
             input / output towards the given Unix FIFOs. This API is
             experimental but should allow quite a few advantages to
             some users willing to perform speculative execution.
             (#210 , improves #202 , @ejgallego)
 - [serapi]  Fix missing newline to separate goals (#235, fixes #231, @ejgallego)

## Version 0.12.0:

 * [general] (!) support Coq 8.12, main changes upstream related to
             the representation of numerals and notations.
             The rest of the interface does remain relative stable.
             (@ejgallego).

## Version 0.11.1:

 * [general] Require dune >= 2.0 (@ejgallego, ??)
 * [serapi]  New query `Comments` to return all comments in a document
             (@ejgallego, #20? , (partially) fixes #191 , #200 )
 * [general] Coq's error recovery is now disabled by default
             (@ejgallego , fixes #201)
 * [general] New option `--error-recovery` to enable error recovery
             (@ejgallego , #203)
 * [general] Bump sexplib dependency to v0.13 (@ejgallego , #204)
             Fixes incorrect change in #194.
 * [sertop]  Set default value of allow-sprop to be true in agreement with upstream coq v8.11
             and added option '--disallow-sprop' to optionally switch it off
			 (--disallow-sprop forbids using the proof irrelevant SProp sort)
             (#199, @pestun)
 * [sertop]  Set default value of allow-sprop to be true in agreement with upstream coq v8.11
             and added option '--disallow-sprop' to optionally switch it off
			 (--disallow-sprop forbids using the proof irrelevant SProp sort)
             (@pestun , #199)
 * [sertop]  Added option `--topfile` to `sertop` to set top name from
             a filename (#197, @pestun)
 * [deps]    Require sexplib >= 0.12 , fixed deprecation warnings
             (#194, @ejgallego)
 * [general] SerAPI is now tested with OCaml 4.08 and 4.09 (#195 , @ejgallego)
 * [sertop ] Forward port sername from 0.7.1 (@ejgallego)
 * [serlib ] Fix #212 "Segfault on universes" (@ejgallego, reported by @cpitclaudel , #214)
 * [serapi ] Fix #221 "Support COQPATH" (@ejgallego, reported by @cpitclaudel , #224)
 * [sertop ] Fix #222 "Support --indices-matter" (@ejgallego, reported by @cpitclaudel , #223)
 * [sertop ] Fix "Stack overflow in main loop" (@pestun , #216)

## Version 0.11.0:

 * [general] (!) support Coq 8.11, a few datatypes have changed, in
             particular `CoqAst` handles locations as an AST node, and
             the kernel type includes primitive floats (@ejgallego).
 * [general] (!) Now the `sertop` and `serapi` OCaml libraries are
             built packed, we've also bumped their compat version number
             (#192 @ejgallego)

## Version 0.7.1:

 * [sertop ] Add `sername` program for batch serialization elaborated terms
             Note that this utility will be deprecated in future versions,
             to be subsumed by `Query`.
             (#207, @palmskog, with help from @ejgallego)
 * [serlib ] Expose `QueryUtil.info_of_id` and `gen_pp_obj` in `serapi_protocol.mli` to enable
             using them in `sername` to retrieve serialized body-type pairs (@palmskog)
 * [general] Improved compat with Jane Street v0.13 toolchain
 * [serlib ] Only use `ssreflect` from Coq in tests (@ejgallego)

## Version 0.7.0:

 * [general] (!) support Coq 8.10,
 * [serapi]  (!) `Goals` query return type has been modified due to
             upstream changes. (@ejgallego)
 * [serlib]  Complete (hopefully) serialization for ssreflect ASTs.
             (#73 @ejgallego)
 * [general] Drop support for OCaml < 4.07 (#140 @ejgallego)
 * [serlib ] JSON serialization for kernel and AST terms (@ejgallego)
 * [serapi ] Add `Complete` support (@ejgallego
             c.f. https://github.com/coq/coq/pull/8766)
 * [serlib ] Serlib is now built as a wrapped module (@ejgallego)
 * [serapi ] (!) Goals info has been extended to print name metadata if available,
             cc #151 (@ejgallego , suggested by @cpitclaudel)
 * [serlib ] JSON support for vernac_expr (@ejgallego)
 * [sertop ] (!) Do as Coq upstream and load Coq's stdlib with `-R` (closes #56)
 * [sertop ] Follow Coq upstream and unset `indices_matter` (closes #157,
             thanks to @palmskog for the report)
 * [serapi ] (!) Improve CoqExn answer to have pretty-printed message (improves #162,
             thanks to @cpitclaudel for the request)
 * [serlib ] (!) Fix capitalization conventions for a few types in `Names`
             (closes #167 thanks to @corwin-of-amber for the report)
 * [serapi ] (!) Add bullet suggest information to goal query (@corwin-of-amber)
 * [sertop ] Add `--no_prelude` option (closes #176, @ejgallego, request of @darbyhaller)
 * [serlib ] (!) Add index to `MBId` serialization (fixes #150, @ejgallego)
 * [serapi ] (!) Add `sid` parameter to `Print` (helps #150, @ejgallego, reported by @cpitclaudel)
 * [sertop ] Add `sertok` program for batch serialization of tokens and their source locations (@palmskog)
 * [serapi ] (!) Add string-formatted messages to `CoqExn` and `Message`
             (@ejgallego closes #184 , closes #162)

## Version 0.6.1:

 * [serapi ] Add `Parse` command to parse a sentence; c.f.
             https://github.com/ejgallego/coq-serapi/issues/117
             (@ejgallego) (cc: @yangky11)
 * [sercomp] Add "print" `--mode` to print the input Coq document
             (@ejgallego) (cc: @Ptival)
 * [serlib ] Serialize `Universe.t` (@ejgallego, request by @yangky11)
 * [sercomp] Merge `sercomp` and `compser`, add `--input` parameter to `sercomp`
             (@palmskog) (cc: @ejgallego)
 * [serlib ] Much improved support for serialization of `Environ.env`
             (@yangky11 and @ejgallego c.f. #118)
 * [serapi ] Make sure every command ends with `Completed`, even if it produced
             an exception (@brando90 and @ejgallego c.f. #124)
 * [sercomp] Add `--mode=kexp` to output the final kernel environment.
             (@ejgallego c.f. #119)
 * [serlib ] Serialize more internal environment fields (@ejgallego c.f. #119)
 * [serlib ] Improvements in serialization org (@ejgallego)
 * [serlib ] Serialize kernel entries (@ejgallego @palmskog)
 * [serlib ] Fix critical bug on `Constr` deserialization; reported by @palmskog,
             fix by @SkySkimmer.
 * [sertop]  Fix backtrace printing when using `--debug` (@ejgallego)
 * [serlib ] Don't serialize VM values (@ejgallego, bug report by @palmskog)
 * [serapi ] Output location on tokenization (@ejgallego , idea by @palmskog)
 * [serapi ] Add basic documentation of the protocol (@ejgallego cc #109)

## Version 0.6.0:

 * [general] support Coq 8.9,
 * [general] SerAPI now uses Dune as a build system,
 * [opam]   install `sertop.el`,
 * [serlib] support to serialize kernel environments,
 * [serapi] new query `Env` that tries to print the current kernel environment,
 * [serlib] correct field names for `CAst`,
 * [serlib] more robust support for opaque / non-serializable types (#61, #68).
            Thanks to @palmskog,
 * [serlib] new option `--exn_on_opaque` to raise an exception on
            non-serializable types; closes #61, thanks to @palmskog,
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
             attributes (such as location) (@ejgallego)
 * [serapi]  Add `Assumptions` query, at the suggestion of @Armael
             (@ejgallego)
 * [sercomp] Disable error resilience mode in compilers; semantics are
             a bit dubious see coq/coq#9204 also #94.
             (@ejgallego, report by @palmskog)
 * [sercomp] Add `check` mode to compilers to check all proofs without
             outputting `.vo`. (@palmskog)
 * [sercomp] Add "hacky" `--quick` option to skip checking of opaque
             proofs. (@ejgallego, request by @palmskog)
 * [sercomp] Add `--async_workers` option to set maximum number
             of parallel async workers. (@palmskog)
 * [sertop] Stop linking Coq plugins statically and load `serlib`
            plugins when Coq plugins are loaded instead (@ejgallego,
            review by @palmskog)

## Version 0.5.7:

 * [serlib] Fixed serializers for more tactics data, add support for
   `ground` plugin (#68). Thanks again to @palmskog for the report.

## Version 0.5.6:

 * [serlib] Fixed serializers for some tactics data (#66) Thanks to
   @palmskog for the report.

## Version 0.5.5:

 * [serlib] Be more lenient when parsing back `Id.t` as to accommodate
   hacks in the Coq AST (#64) Thanks to @palmskog for the report.

## Version 0.5.4:

 * [serlib] Fix critical bug in handling of abstract type (#60)

## Version 0.5.3:

 * [sertop] Support for `-I` option (`--ml-include-path`).

## Version 0.5.2:

 * [serlib] Compatibility with OCaml 4.07.0 [problems with `Stdlib` packing]

## Version 0.5.1:

 * [serlib] (basic) support for serialization of the ssreflect grammar,
 * [serapi] `(Query () (Ast n))` is now `(Query ((sid n)) Ast)`,
 * [serapi] remove broken deprecated `SetOpt` and `LibAdd` commands,
 * [doc] Improved man page.
 * [js] Miscellaneous improvements on the js build.

## Version 0.5.0:

 * [general] support Coq 8.8, use improved document API,
 * [sertop] By default `sertop` will create a new document with `doc_id` 0,
 * [sertop] new debug options, see `sertop --help`.

## Version 0.4:

 * [general] support Coq 8.7 , make use of improved upstream API,
 * [sertop] support `-R` and `-Q` options, note the slightly different
   syntax wrt Coq upstream: `-R dir,path` in place of `-R dir path`,
 * [serlib] support serialization of generic arguments [#41],
 * [serapi] `(ReadFile file)`: hack to load a completed file.

## Version 0.2:

 * Better Query/Object system.

## Version 0.1:

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

## Version 0.03:

 * **[done]** Implicit arguments.
 * **[done]** Coq Workers support.
 * **[done]** Advanced Sentence splitting `(Parse (Sentence string))`, which can handle the whole document.

## Version 0.02:

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
