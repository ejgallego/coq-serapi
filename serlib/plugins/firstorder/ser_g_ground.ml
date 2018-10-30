open Ground_plugin
open Sexplib.Conv

module Loc = Ser_loc
module Libnames = Ser_libnames
module Misctypes = Ser_misctypes
module Globnames = Ser_globnames


type h1 = Libnames.reference list
[@@deriving sexp]

type h2 = Globnames.global_reference Loc.located Misctypes.or_var list
[@@deriving sexp]

type h3 = Globnames.global_reference list
[@@deriving sexp]

let ser_wit_firstorder_using :
  (Libnames.reference list,
   Globnames.global_reference Loc.located Misctypes.or_var list,
   Globnames.global_reference list) Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = sexp_of_h1;
    raw_des = h1_of_sexp;

    glb_ser = sexp_of_h2;
    glb_des = h2_of_sexp;

    top_ser = sexp_of_h3;
    top_des = h3_of_sexp;
  }

let register () =
  Ser_genarg.register_genser G_ground.wit_firstorder_using ser_wit_firstorder_using
