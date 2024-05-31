(* Serialization for agent types *)

(* Implement State.t and Env.t serialization methods *)
module State = Obj_map.Make (Petanque.Agent.State)
module Env = Obj_map.Make (Petanque.Agent.Env)

(* The typical protocol dance *)

module Stdlib = struct
  module Result = struct
    include Stdlib.Result

    type ('a, 'e) t = [%import: ('a, 'e) Stdlib.Result.t] [@@deriving yojson]
  end
end

(* What a mess result stuff is, we need this in case result is installed, as
   then the types below will be referenced as plain result ... *)
module Result = Stdlib.Result

module Error = struct
  type t = [%import: Petanque.Agent.Error.t] [@@deriving yojson]
end

module Run_result = struct
  type 'a t = [%import: 'a Petanque.Agent.Run_result.t] [@@deriving yojson]
end

module R = struct
  type 'a t = [%import: 'a Petanque.Agent.R.t] [@@deriving yojson]
end

module Goals = struct
  type t = string Lsp.JCoq.Goals.reified_pp option [@@deriving yojson]
end

module Lang = struct
  module Range = struct
    type t = Lsp.JLang.Range.t [@@deriving yojson]
  end
end

module Premise = struct
  type t = [%import: Petanque.Agent.Premise.t] [@@deriving yojson]
end
