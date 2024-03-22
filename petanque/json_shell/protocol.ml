(* uhh *)
module Result = struct
  include Result

  type ('a, 'e) t = ('a, 'e) Result.t =
    | Ok of 'a
    | Error of 'e
  [@@deriving yojson]
end

module A = Petanque.Agent

(* We follow the methodology of SerAPI, we have a shell *)
module Command = struct
  type t =
    | Start of
        { uri : string
        ; thm : string
        }
    | Run_tac of
        { st : State.t
        ; tac : string
        }
    | Goals of { st : State.t }
  [@@deriving yojson]
end

module Goals = struct
  type t = string [@@deriving yojson]
end

module Answer = struct
  type t =
    | Start of (State.t, string) Result.t
    | Run_tac of (State.t, string) Result.t
    | Goals of (Goals.t, string) Result.t
  [@@deriving yojson]
end
