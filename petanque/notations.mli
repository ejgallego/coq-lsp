module Notation : sig
  type t =
    { locations: Loc.t list
    ; path: string
    ; secpath: string
    ; notation: string
    ; scope: string option
    } [@@deriving yojson]

  val to_yojson : t -> Yojson.Safe.t
  val of_yojson : Yojson.Safe.t -> (t, string) result
end

val coq_list_notations_in_statement :
     token:Coq.Limits.Token.t
  -> intern:Library.Intern.t
  -> st:Coq.State.t
  -> Coq.Ast.t
  -> (Notation.t list, Loc.t) Coq.Protect.E.t
