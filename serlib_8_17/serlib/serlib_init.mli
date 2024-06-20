type options =
  { omit_loc : bool
  ; omit_att : bool
  ; omit_env : bool
  ; exn_on_opaque : bool
  }

val init : options:options -> unit

