type options =
  { omit_loc : bool
  ; omit_att : bool
  ; exn_on_opaque : bool
  }

val init : options:options -> unit

