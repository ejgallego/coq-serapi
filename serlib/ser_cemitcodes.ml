type to_patch_substituted =
  [%import: Cemitcodes.to_patch_substituted]

let sexp_of_to_patch_substituted = Serlib_base.sexp_of_opaque ~typ:"Cemitcodes.to_patch_substituted"
let to_patch_substituted_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Cemitcodes.to_patch_substituted"
