module type Chans = sig
  val ic : in_channel
  val oc : Format.formatter
  val trace : ?verbose:string -> string -> unit
  val message : lvl:int -> message:string -> unit
end

open Protocol

module S (C : Chans) : sig
  val init : Init.Params_.t -> (Init.Response_.t, string) result
  val start : Start.Params_.t -> (Start.Response_.t, string) result
  val run_tac : RunTac.Params_.t -> (RunTac.Response_.t, string) result
  val goals : Goals.Params_.t -> (Goals.Response_.t, string) result
  val premises : Premises.Params_.t -> (Premises.Response_.t, string) result
end
