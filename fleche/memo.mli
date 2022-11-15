(************************************************************************)
(* Flèche Document Manager                                              *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2022 Inria           -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
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
val input_info : Lang.Ast.t * Lang.State.t -> string

val interp_command :
     st:Lang.State.t
  -> fb_queue:Lang.Message.t list ref
  -> Lang.Ast.t
  -> Lang.State.t Lang.Interp.interp_result Stats.t

val mem_stats : unit -> int
val load_from_disk : file:string -> unit
val save_to_disk : file:string -> unit

module CacheStats : sig
  val reset : unit -> unit
  val stats : unit -> string
end
