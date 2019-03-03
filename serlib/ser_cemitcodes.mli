open Sexplib

type to_patch_substituted = Cemitcodes.to_patch_substituted

val sexp_of_to_patch_substituted : to_patch_substituted -> Sexp.t
val to_patch_substituted_of_sexp : Sexp.t -> to_patch_substituted
