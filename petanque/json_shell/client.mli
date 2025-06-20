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

  val toc :
    TableOfContents.Params.t -> (TableOfContents.Response.t, string) result

  val get_root_state :
    GetRootState.Params.t -> (GetRootState.Response.t, string) result

  val get_state_at_pos :
    GetStateAtPos.Params.t -> (GetStateAtPos.Response.t, string) result

  val start : Start.Params.t -> (Start.Response.t, string) result
  val run : RunTac.Params.t -> (RunTac.Response.t, string) result
  val goals : Goals.Params.t -> (Goals.Response.t, string) result
  val premises : Premises.Params.t -> (Premises.Response.t, string) result

  val state_equal :
    StateEqual.Params.t -> (StateEqual.Response.t, string) result

  val state_hash : StateHash.Params.t -> (StateHash.Response.t, string) result

  val state_proof_equal :
    StateProofEqual.Params.t -> (StateProofEqual.Response.t, string) result

  val state_proof_hash :
    StateProofHash.Params.t -> (StateProofHash.Response.t, string) result

  val ast : PetAst.Params.t -> (PetAst.Response.t, string) result
  val ast_at_pos : AstAtPos.Params.t -> (AstAtPos.Response.t, string) result

  val definition : Definition.Params.t -> (Definition.Response.t, string) result
end
