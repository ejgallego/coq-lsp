(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** Setups the server configuration, takes the list of settings as a JSON dict *)
val do_settings : (string * Yojson.Safe.t) list -> unit

(** Returns answer request + workspace root directory *)
val do_initialize :
  params:(string * Yojson.Safe.t) list -> Yojson.Safe.t * string list
