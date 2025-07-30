(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)

(* Some issues due to different API in clients... *)
module type Point = sig
  type t

  val in_range : ?range:Lang.Range.t -> t -> bool
  val gt_range : ?range:Lang.Range.t -> t -> bool

  (** [to_offset] will help to resolve a position from for example (line,col) to
      an offset, but in some case requires a lookup method. *)
  type offset_table = string

  val to_offset : t -> offset_table -> int
  val to_string : t -> string
end

module LineCol : Point with type t = int * int
module Offset : Point with type t = int

type approx =
  | Exact  (** Exact on point *)
  | PrevIfEmpty  (** If no match, return prev *)
  | Prev  (** Always return previous node *)

(** Located queries *)
module type S = sig
  module P : Point

  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  val node : (approx, Doc.Node.t) query
end

module LC : S with module P := LineCol
module O : S with module P := Offset

(** We move towards a more modular design here, for preprocessing *)
module Goals : sig
  val get_goals_unit : st:Coq.State.t -> (unit, Pp.t) Coq.Goals.reified option

  val get_goals :
       st:Coq.State.t
    -> (Environ.env * Evd.evar_map * EConstr.t, Pp.t) Coq.Goals.reified option

  type 'a printer =
    token:Coq.Limits.Token.t -> Environ.env -> Evd.evar_map -> EConstr.t -> 'a

  val to_pp : Pp.t printer

  val goals :
       token:Coq.Limits.Token.t
    -> pr:'a printer
    -> st:Coq.State.t
    -> (('a, Pp.t) Coq.Goals.reified option, Loc.t) Coq.Protect.E.t

  val program : st:Coq.State.t -> Declare.OblState.View.t Names.Id.Map.t
end

module Completion : sig
  val candidates :
       token:Coq.Limits.Token.t
    -> st:Coq.State.t
    -> string
    -> (string list option, Loc.t) Coq.Protect.E.t
end
