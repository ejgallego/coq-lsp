module type Chans = sig
  val ic : in_channel
  val oc : Format.formatter
  val trace : ?verbose:string -> string -> unit
  val message : lvl:int -> message:string -> unit
end

open Protocol

module S (C : Chans) : sig
  val init : Init.Params.t -> (Init.Response.t, string) result
  val start : Start.Params.t -> (Start.Response.t, string) result
  val run_tac : RunTac.Params.t -> (RunTac.Response.t, string) result
  val goals : Goals.Params.t -> (Goals.Response.t, string) result
  val premises : Premises.Params.t -> (Premises.Response.t, string) result
end
