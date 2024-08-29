(* Serialization for agent types *)

(* Implement State.t and Env.t serialization methods *)
module State = Obj_map.Make (Petanque.Agent.State)

module Inspect = struct
  type t = [%import: Petanque.Agent.State.Inspect.t] [@@deriving yojson]
end

(* The typical protocol dance *)
module Error = struct
  type t = [%import: Petanque.Agent.Error.t] [@@deriving yojson]
end

module Run_opts = struct
  type t = [%import: Petanque.Agent.Run_opts.t] [@@deriving yojson]
end

module Run_result = struct
  type 'a t = [%import: 'a Petanque.Agent.Run_result.t] [@@deriving yojson]
end

(* Both are needed as of today *)
module Stdlib = Lsp.JStdlib
module Result = Stdlib.Result

module R = struct
  type 'a t = [%import: 'a Petanque.Agent.R.t] [@@deriving yojson]
end

module Goals = struct
  type t = string Lsp.JCoq.Goals.reified_pp option [@@deriving yojson]
end

module Lang = Lsp.JLang

module Premise = struct
  module Info = struct
    type t = [%import: Petanque.Agent.Premise.Info.t] [@@deriving yojson]
  end

  type t = [%import: Petanque.Agent.Premise.t] [@@deriving yojson]
end
