(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Limits API                             *)
(*************************************************************************)

(* This is a wrapper for memprof-limits libs *)
module type Intf = sig
  module Token : sig
    type t

    val create : unit -> t
    val set : t -> unit
    val is_set : t -> bool
  end

  val start : unit -> unit
  val limit : token:Token.t -> f:('a -> 'b) -> 'a -> ('b, exn) Result.t
  val name : unit -> string
  val available : bool
end

module Coq : Intf
module Mp : Intf
include Intf

type backend =
  | Coq
  | Mp

(** *Must* be called *only* once *)
val select : backend -> unit

(** If [None] will pick the best backend, must be called only once *)
val select_best : backend option -> unit

val create_atomic : unit -> Token.t
