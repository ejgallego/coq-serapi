open Recdef_plugin
open Sexplib.Conv

let ser_wit_fun_scheme_arg :
  (Names.variable * Libnames.qualid * Sorts.family, unit, unit)
    Ser_genarg.gen_ser =
  Ser_genarg.{
    raw_ser = sexp_of_triple Ser_names.sexp_of_variable Ser_libnames.sexp_of_qualid Ser_sorts.sexp_of_family;
    raw_des = triple_of_sexp Ser_names.variable_of_sexp Ser_libnames.qualid_of_sexp Ser_sorts.family_of_sexp;

    glb_ser = sexp_of_unit;
    glb_des = unit_of_sexp;

    top_ser = sexp_of_unit;
    top_des = unit_of_sexp;
  }

let register () =
  Ser_genarg.register_genser G_indfun.wit_fun_scheme_arg ser_wit_fun_scheme_arg;
  ()
