module Stats : sig
  type 'a t =
    { res : 'a
    ; cache_hit : bool
    ; memory : int
    ; time : float
    }
end

module Init : sig
  type t = Coq.State.t * Coq.Workspace.t * Lang.LUri.File.t

  val eval : t -> (Coq.State.t, Loc.t) Coq.Protect.E.t
end

module Interp : sig
  type t = Coq.State.t * Coq.Ast.t

  (** Interpret a command, possibly memoizing it *)
  val eval : t -> Coq.State.t Coq.Interp.interp_result Stats.t

  (** Stats *)
  val stats : unit -> int

  (** debug *)
  val input_info : t -> string
end

module Admit : sig
  type t = Coq.State.t

  val eval : t -> (Coq.State.t, Loc.t) Coq.Protect.E.t
end

module CacheStats : sig
  val reset : unit -> unit
  val stats : unit -> string
end
