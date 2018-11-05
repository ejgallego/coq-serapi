open Sexplib.Std

type vernac_flag =
  [%import: Attributes.vernac_flag]
and
 vernac_flag_value =
  [%import: Attributes.vernac_flag_value]
and vernac_flags =
  [%import: Attributes.vernac_flags]
  [@@deriving sexp]

type deprecation =
  [%import: Attributes.deprecation]
  [@@deriving sexp]
