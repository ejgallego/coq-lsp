(** Returns answer request + workspace root directory *)
val do_initialize :
  params:(string * Yojson.Safe.t) list -> Yojson.Safe.t * string
