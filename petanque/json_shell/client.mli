open Petanque_json

module type Chans = sig
  val ic : in_channel
  val oc : Format.formatter
  val trace : ?verbose:string -> string -> unit
  val message : lvl:int -> message:string -> unit
end

open Protocol
open Protocol_shell

module S (C : Chans) : sig
  val set_workspace :
    SetWorkspace.Params.t -> (SetWorkspace.Response.t, string) result

  val start : Start.Params.t -> (Start.Response.t, string) result
  val run : RunTac.Params.t -> (RunTac.Response.t, string) result
  val goals : Goals.Params.t -> (Goals.Response.t, string) result
  val premises : Premises.Params.t -> (Premises.Response.t, string) result

  val state_equal :
    StateEqual.Params.t -> (StateEqual.Response.t, string) result

  val state_hash : StateHash.Params.t -> (StateHash.Response.t, string) result
end
