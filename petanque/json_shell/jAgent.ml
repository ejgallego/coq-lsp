(* Serialization for agent types *)

(* Implement State.t and Env.t serialization methods *)
module State = Obj_map.Make (Petanque.Agent.State)
module Env = Obj_map.Make (Petanque.Agent.Env)

(* The typical protocol dance *)

module Result = struct
  include Result

  type ('a, 'e) t = [%import: ('a, 'e) Result.t] [@@deriving yojson]
end

module Error = struct
  type t = [%import: Petanque.Agent.Error.t] [@@deriving yojson]
end

module R = struct
  type 'a t = [%import: 'a Petanque.Agent.R.t] [@@deriving yojson]
end

module Goals = struct
  type t = string Lsp.JCoq.Goals.reified_pp option [@@deriving yojson]
end
