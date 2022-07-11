(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

module Stats : sig
  type 'a t =
    { res : 'a
    ; cache_hit : bool
    ; memory : int
    ; time : float
    }
end

(* debug *)
val input_info : Coq.Ast.t * Coq.State.t -> string

val interp_command :
     st:Coq.State.t
  -> fb_queue:Coq.Message.t list ref
  -> Coq.Ast.t
  -> Coq.State.t Coq.Interp.interp_result Stats.t

val parse :
     mode:Pvernac.proof_mode option
  -> st:Vernacstate.Parser.t
  -> text:string (* for the cache *)
  -> Pcoq.Parsable.t
  -> Coq.Ast.t option Coq.Protect.R.t * float

val mem_stats : unit -> int
val load_from_disk : file:string -> unit
val save_to_disk : file:string -> unit

module CacheStats : sig
  val reset : unit -> unit
  val stats : unit -> string
end
