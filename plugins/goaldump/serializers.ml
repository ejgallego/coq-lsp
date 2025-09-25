(* Just to bring the serializers in scope *)
open Sexplib.Conv

(* Overlay just to add sexp serialization of lang structures, if we keep sexp we
   should move this to its proper library *)
module Lang = struct
  module Point = struct
    type t = [%import: Lang.Point.t] [@@deriving yojson, sexp]
  end

  module Range = struct
    type t = [%import: (Lang.Range.t[@with Lang.Point.t := Point.t])]
    [@@deriving yojson, sexp]
  end
end

module Coq = struct
  module Loc = Serlib.Ser_loc
  module Names = Serlib.Ser_names
  module Evar = Serlib.Ser_evar
  module Evar_kinds = Serlib.Ser_evar_kinds

  module Ast = struct
    include Fleche_lsp.JCoq.Ast

    let sexp_of_t x =
      Serlib.Ser_vernacexpr.sexp_of_vernac_control (Coq.Ast.to_coq x)
  end

  module Goals = struct
    module Reified_goal = struct
      type 'a hyp = [%import: 'a Coq.Goals.Reified_goal.hyp]
      [@@deriving yojson, sexp]

      type info = [%import: Coq.Goals.Reified_goal.info]
      [@@deriving yojson, sexp]

      type 'a t = [%import: 'a Coq.Goals.Reified_goal.t]
      [@@deriving yojson, sexp]
    end

    module Goals_ = struct
      type ('a, 'pp) t =
        { goals : 'a list
        ; stack : ('a list * 'a list) list
        ; bullet : 'pp option
        ; shelf : 'a list
        ; given_up : 'a list
        }
      [@@deriving yojson, sexp]

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

    let sexp_of_t f pp g = Goals_.to_ g |> Goals_.sexp_of_t f pp

    type 'pp reified_pp = ('pp Reified_goal.t, 'pp) t
    [@@deriving yojson, sexp_of]
  end
end
