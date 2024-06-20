module Stats : sig
  type t =
    { stats : Stats.t
    ; time_hash : float
          (** Time in hashing consumed in the original execution *)
    ; cache_hit : bool  (** Whether we had a cache hit *)
    }

  val zero : t
end

module Intern : sig
  val clear : unit -> unit
end

(** Flèche memo / cache tables, with some advanced features *)
module type S = sig
  type input

  (** For now, to generalize later if needed *)
  type output

  (** [eval i] Eval an input [i] *)
  val eval :
    token:Coq.Limits.Token.t -> input -> (output, Loc.t) Coq.Protect.E.t

  (** [eval i] Eval an input [i] and produce stats *)
  val evalS :
       token:Coq.Limits.Token.t
    -> input
    -> (output, Loc.t) Coq.Protect.E.t * Stats.t

  (** [size ()] Return the cache size in words, expensive *)
  val size : unit -> int

  (** [freqs ()]: (sorted) histogram *)
  val all_freqs : unit -> int list

  (** [stats ()]: hashtbl stats *)
  val stats : unit -> Hashtbl.statistics

  (** debug data for input *)
  val input_info : input -> string

  (** clears the cache *)
  val clear : unit -> unit
end

(** Document creation cache *)
module Init :
  S
    with type input = Coq.State.t * Coq.Workspace.t * Lang.LUri.File.t
     and type output = Coq.State.t

(** Vernacular evaluation cache, invariant w.r.t. Coq's Ast locations, results
    are repaired. *)
module Interp :
  S with type input = Coq.State.t * Coq.Ast.t and type output = Coq.State.t

(** Require evaluation cache, also invariant w.r.t. locations inside
    [Coq.Ast.Require.t] *)
module Require :
  S
    with type input = Coq.State.t * Coq.Files.t * Coq.Ast.Require.t
     and type output = Coq.State.t

(** Admit evaluation cache *)
module Admit : S with type input = Coq.State.t and type output = Coq.State.t

module GlobalCacheStats : sig
  val reset : unit -> unit

  (** Returns the hit ratio of the cache, etc... *)
  val stats : unit -> string
end

(** Size of all caches, very expensive *)
val all_size : unit -> int
