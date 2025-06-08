(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq Glob API                          *)
(*************************************************************************)

(** A glob file that was read and parsed successfully *)
type t

(* Input is a .glob file *)
val open_file : string -> (t, string) Result.t

module Info : sig
  type t =
    { kind : string
    ; offset : int * int
    }
end

val get_info : t -> string -> Info.t option
