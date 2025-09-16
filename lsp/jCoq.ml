module Loc = Serlib.Ser_loc
module Names = Serlib.Ser_names
module Evar = Serlib.Ser_evar
module Evar_kinds = Serlib.Ser_evar_kinds

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

  let str = Pp.str
  let string_of_ppcmds = Pp.string_of_ppcmds
  let to_string = Pp.string_of_ppcmds
  let to_yojson x = to_yojson (pp_opt x)
end

module Goals = struct
  module Reified_goal = struct
    type 'a hyp = [%import: 'a Coq.Goals.Reified_goal.hyp] [@@deriving yojson]
    type info = [%import: Coq.Goals.Reified_goal.info] [@@deriving yojson]
    type 'a t = [%import: 'a Coq.Goals.Reified_goal.t] [@@deriving yojson]
  end

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

    let of_ { goals; stack; bullet; shelf; given_up } =
      { Coq.Goals.goals; stack; bullet; shelf; given_up }
  end

  type ('a, 'pp) t = ('a, 'pp) Coq.Goals.t

  let to_yojson f pp g = Goals_.to_ g |> Goals_.to_yojson f pp

  let of_yojson f pp j =
    let open Ppx_deriving_yojson_runtime in
    Goals_.of_yojson f pp j >|= Goals_.of_

  type ('g, 'pp) reified = [%import: ('g, 'pp) Coq.Goals.reified]
  [@@deriving yojson]
end

module Ast = struct
  type t = Coq.Ast.t

  (* XXX: Better catch the exception below, but this requires a new SerAPI
     release *)
  let () = Serlib.Serlib_base.exn_on_opaque := false

  let to_yojson x =
    Serlib.Ser_vernacexpr.vernac_control_to_yojson (Coq.Ast.to_coq x)

  let of_yojson x =
    Serlib.Ser_vernacexpr.vernac_control_of_yojson x
    |> Result.map Coq.Ast.of_coq
end

module Declare = struct
  module OblState = struct
    module View = struct
      module Obl = struct
        type t = [%import: Declare.OblState.View.Obl.t] [@@deriving to_yojson]

        let of_yojson obj =
          Serlib.Serlib_base.opaque_of_yojson ~typ:"Declare.OblState.View.Obl.t"
            obj
      end

      type t = [%import: Declare.OblState.View.t] [@@deriving to_yojson]

      let of_yojson obj =
        Serlib.Serlib_base.opaque_of_yojson ~typ:"Declare.OblState.View.t" obj
    end
  end
end
