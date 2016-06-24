(* JsCoq
 * Copyright (C) 2016 Emilio Gallego / Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq.
 *
 * Due to the large size of Coq libraries, we perform caching and lazy
 * loading in the browser.
*)

open Js

(** [init lib_path available_pkg init_pkgs]
    gather package list [available_pkg] and start preloading
    [init_pkgs] from directory [lib_path]
  *)
val init : js_string t -> js_string t js_array t -> js_string t js_array t -> unit

(** [load_pkg pkg] load package [pkg] *)
val load_pkg : string -> unit

(** [coq_resource_req url] query the manager's cache for object [url] *)
val coq_vo_req  : string -> string option

(** [coq_cma_link cma] dynlinks the bytecode plugin [cma] *)
val coq_cma_link : string -> unit
