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

  let to_string = Pp.string_of_ppcmds
  let to_yojson x = to_yojson (pp_opt x)
end

module Goals = struct
  type 'a hyp = [%import: 'a Coq.Goals.hyp] [@@deriving yojson]
  type info = [%import: Coq.Goals.info] [@@deriving yojson]

  type 'a reified_goal = [%import: 'a Coq.Goals.reified_goal]
  [@@deriving yojson]

  type 'a goals = [%import: 'a Coq.Goals.goals] [@@deriving yojson]
  type reified_pp = Pp.t reified_goal goals [@@deriving yojson]
end
