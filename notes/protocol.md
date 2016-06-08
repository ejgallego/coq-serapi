# Notes on a Coq Protocol for IDEs

These are some notes on the JsCoq Coq Protocol, which IOVH should work
for other IDEs too.

## State of the art:

### Emacs/ProofGeneral

The current interface used by Emacs/ProofGeneral (and possibly other
tools) is `string -> string` based interface with a bit of extra
information.

This approach is a bit fragile, as PG is fully coupled to the printer
and parser, and must do it own printing/parsing of Coq's output.

This design choice also has the the effect to require a new Vernacular
command everytime an IDE needs some functionality see coq:coq#64.

A few examples of the Vernacular situation are:

```ocaml
type showable =
  | ShowGoal of goal_reference
  | ShowGoalImplicitly of int option
  | ShowProof
  | ShowNode
  | ShowScript
  | ShowExistentials
  | ShowUniverses
  | ShowTree
  | ShowProofNames
  | ShowIntros of bool
  | ShowMatch of lident
  | ShowThesis
```

```ocaml
type printable =
  | PrintTables
  | PrintFullContext
  | PrintSectionContext of reference
  | PrintInspect of int
  | PrintGrammar of string
  | PrintLoadPath of DirPath.t option
  | PrintModules
  | PrintModule of reference
  | PrintModuleType of reference
  | PrintNamespace of DirPath.t
  | PrintMLLoadPath
  | PrintMLModules
  | PrintDebugGC
  | PrintName of reference or_by_notation
  | PrintGraph
  | PrintClasses
  | PrintTypeClasses
  | PrintInstances of reference or_by_notation
  | PrintLtac of reference
  | PrintCoercions
  | PrintCoercionPaths of class_rawexpr * class_rawexpr
  | PrintCanonicalConversions
  | PrintUniverses of bool * string option
  | PrintHint of reference or_by_notation
  | PrintHintGoal
  | PrintHintDbName of string
  | PrintRewriteHintDbName of string
  | PrintHintDb
  | PrintScopes
  | PrintScope of string
  | PrintVisibility of string option
  | PrintAbout of reference or_by_notation*int option
  | PrintImplicit of reference or_by_notation
  | PrintAssumptions of bool * bool * reference or_by_notation
  | PrintStrategy of reference or_by_notation option
```

Not much more can be said.

### CoqIDE

CoqIDE has done a significant effort to provide a more structured API
to IDEs, which is documented in (`interface.ml`)[ide/interface.ml].

Unfolding the types we get the current API:

```ocaml
type handler = {
  add     : (string * edit_id) * (state_id * verbose)
         -> state_id * ((unit, state_id) union * string);

  edit_at : state_id
         -> (unit, state_id * (state_id * state_id)) union;

  query   : string * state_id
         -> string;

  goals   : unit
         -> goals option;

  evars   : unit
         -> evar list option;

  hints   : unit
         -> (hint list * hint) option;

  status  : bool
         -> status;

  search  : search_flags
         -> string coq_object list;

  get_options : unit
             -> (option_name * option_state) list;

  set_options : (option_name * option_value) list
             -> unit

  mkcases     : string
             -> string list list;

  about       : unit
             -> coq_info;

  stop_worker : string ->
                unit;

  print_ast   : string
             -> Xml_datatype.xml;

  annotate    : string
             -> Xml_datatype.xml;

  handle_exn  : Exninfo.iexn
             -> state_id * location * string;

  init        : string option
             -> state_id;

  quit        : unit
             -> unit;

  (* Retrocompatibility stuff *)
  interp      : (raw * verbose) * string
             -> state_id * (string,string) Util.union;
}
```

This is looking much better! Some comments about the API:

- Serialization of data structures is intertwined with the API. This
  also produces duplication.
- Synchronous/asynchronous calling convention is hidden in a different
  layer.
- It doesn't reflect what feedback a call may produce.
- It may be difficult to extend in a compatible way.
- It doesn't support streaming of results.
- It doesn't support per-command options.

Also, error handling is not very clear in general.

## Main design motto:

We want to propose an evolution of the above API suited for use in
jsCoq. Our main design mottu are:

- Separate API from RPC.
- Separate data serialization from API.
- Favor extensibility.
- Be fully asynchronous, support streaming.

This last point is likely the most debatable one; however in principle
any Coq operation can be quite expensive so we think it is a good
approach to have the IDEs assume a full asynchronous operation.

## Main use cases:

Aside these foundational principles, we may ask us the somewhat
important question, _what do IDEs need?_

Broadly speaking, IDEs perform 3 kind of operations:

- Requesting Coq to advance in the document.
- Searching/querying for objects.
- Printing/parsing objects.

- "select objects of kind X using criterion Y"
- "print objects of kind X"

Did we forget about "setting options" ? Well, in general IDEs don't
set global options?

  The protocol is based on RPC, thus it guarantees at least call
  completion!

  Should all answers be async?

  Then the IDEs must be programmer in the promise style, and it may
  not complete!

## A First Try:

Two layers:

  + RPC layer (IMAP style?)
  + Message layer: The actual objects in the call.

### Objects:

This includes goals, evars, tactics,

*** Objects [this should be async for sure]:
   + query (with state_id!)
     tactics
     options
     defs == search
     loadpaths
     + plugins can add things here!

#+BEGIN_SRC ocaml
type _ coq_object =
 | Constr : constr -> constr coq_object
 | Tactic : tactic -> tactic coq_object
 | Hint   : tactic -> tactic coq_object
 etc...
#+END_SRC

### The STM: Control

Print could take an ID

*** STM manipulation:
   + add
   + edit
   + commit
   + worker_ctrl/ctrl (quit, init)
   + exn?

### Queries: Search

- Allow query to return a diff.
- Allow query to return objects in different forms: uid refs, printed, raw

Search now operates over objects, criteria?

Filter library, it is strongly typed.

#+BEGIN_SRC ocaml
type _ query =
  | U : int  -> int    query
  | B : int  -> string query
  | C : unit -> unit   query

#+END_SRC

### Printing/Parsing: Display

#+BEGIN_SRC ocaml

+ printer: takes an object
+ parser:  takes an string.


