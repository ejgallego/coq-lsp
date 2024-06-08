(* Serialization for agent types *)

(* Implement State.t and Env.t serialization methods *)
module State = Obj_map.Make (Petanque.Agent.State)
module Env = Obj_map.Make (Petanque.Agent.Env)

(* The typical protocol dance *)

(* What a mess result stuff is, we need this in case result is installed, as
   then the types below will be referenced as plain result ... *)
module Stdlib = struct
  module Result = struct
    include Stdlib.Result

    type ('a, 'e) t = [%import: ('a, 'e) Stdlib.Result.t] [@@deriving yojson]
  end
end

module Result = Stdlib.Result

(* ppx_import < 1.10 hack, for some reason it gets confused with the aliases. *)
module Result_ = Stdlib.Result

module Error = struct
  type t = [%import: Petanque.Agent.Error.t] [@@deriving yojson]
end

module Run_result = struct
  type 'a t = [%import: 'a Petanque.Agent.Run_result.t] [@@deriving yojson]
end

module R = struct
  type 'a t =
    [%import:
      ('a Petanque.Agent.R.t
      [@with
        Stdlib.Result.t := Result_.t;
        Result.t := Result_.t])]
  [@@deriving yojson]
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
  module Info = struct
    type t = [%import: Petanque.Agent.Premise.Info.t] [@@deriving yojson]
  end

  type t =
    [%import:
      (Petanque.Agent.Premise.t
      [@with
        Stdlib.Result.t := Result_.t;
        Result.t := Result_.t])]
  [@@deriving yojson]
end
