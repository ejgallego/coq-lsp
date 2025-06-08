(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq AST API                           *)
(*************************************************************************)

type t

val loc : t -> Loc.t option
val hash : t -> int
val compare : t -> t -> int

module Id : sig
  type t

  val of_string : string -> t
  val of_coq : Names.Id.t -> t
  val to_coq : t -> Names.Id.t

  module Set : CSet.ExtS with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set
end

module Require : sig
  type ast = t

  type t = private
    { from : Libnames.qualid option
    ; export : Vernacexpr.export_with_cats option
    ; mods : (Libnames.qualid * Vernacexpr.import_filter_expr) list
    ; loc : Loc.t option
    ; attrs : Attributes.vernac_flag list
    ; control : Vernacexpr.control_flag list
    }
  [@@deriving hash, compare]

  (** Determine if the Ast is a Require *)
  val extract : ast -> t option
end

module Meta : sig
  type ast = t

  module Command : sig
    type t =
      | AbortAll
      | Back of int
      | ResetInitial
      | ResetName of Names.lident
      | Restart
  end

  type t =
    { command : Command.t
    ; loc : Loc.t option
    ; attrs : Attributes.vernac_flag list
    ; control : Vernacexpr.control_flag list
    }
  [@@deriving hash, compare]

  (** Determine if we are under a meta-command *)
  val extract : ast -> t option
end

(** [make_info ~st ast] Compute info about a possible definition in [ast], we
    need [~st] to compute the type. *)
val make_info :
  st:State.t -> lines:string array -> t -> Lang.Ast.Info.t list option

(** Printing *)
val print : t -> Pp.t

val pp_loc : ?print_file:bool -> Format.formatter -> Loc.t -> unit
val loc_to_string : ?print_file:bool -> Loc.t -> string

(** Unused for now *)
val marshal_in : in_channel -> t

val marshal_out : out_channel -> t -> unit

(** Internal, will go away once the [Lang.t] interface is ready *)
val to_coq : t -> Vernacexpr.vernac_control

val of_coq : Vernacexpr.vernac_control -> t
