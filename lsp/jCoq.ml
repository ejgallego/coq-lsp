module Names = Serlib.Ser_names
module Evar = Serlib.Ser_evar

let rec pp_opt d =
  let open Pp in
  let rec flatten_glue l =
    match l with
    | [] -> []
    | Ppcmd_glue g :: l -> flatten_glue (List.map repr g @ flatten_glue l)
    | Ppcmd_string s1 :: Ppcmd_string s2 :: l ->
      flatten_glue (Ppcmd_string (s1 ^ s2) :: flatten_glue l)
    | x :: l -> x :: flatten_glue l
  in
  unrepr
    (match repr d with
    | Ppcmd_glue [] -> Ppcmd_empty
    | Ppcmd_glue [ x ] -> repr (pp_opt x)
    | Ppcmd_glue l ->
      Ppcmd_glue List.(map pp_opt (map unrepr (flatten_glue (map repr l))))
    | Ppcmd_box (bt, d) -> Ppcmd_box (bt, pp_opt d)
    | Ppcmd_tag (t, d) -> Ppcmd_tag (t, pp_opt d)
    | d -> d)

module Pp = struct
  include Serlib.Ser_pp

  let string_of_ppcmds = Pp.string_of_ppcmds
  let to_string = Pp.string_of_ppcmds
  let to_yojson x = to_yojson (pp_opt x)
end

module Goals = struct
  type 'a hyp = [%import: 'a Coq.Goals.hyp] [@@deriving yojson]
  type info = [%import: Coq.Goals.info] [@@deriving yojson]

  type 'a reified_goal = [%import: 'a Coq.Goals.reified_goal]
  [@@deriving yojson]

  module Goals_ = struct
    type ('a, 'pp) t =
      { goals : 'a list
      ; stack : ('a list * 'a list) list
      ; bullet : 'pp option
      ; shelf : 'a list
      ; given_up : 'a list
      }
    [@@deriving yojson]

    let to_ { Coq.Goals.goals; stack; bullet; shelf; given_up } =
      { goals; stack; bullet; shelf; given_up }
  end

  type 'a goals = 'a Coq.Goals.goals

  let goals_to_yojson f g =
    let pp x = Pp.to_yojson x in
    Goals_.to_ g |> Goals_.to_yojson f pp

  type reified_pp = Pp.t reified_goal goals [@@deriving to_yojson]
end
