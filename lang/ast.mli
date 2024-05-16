module Name : sig
  type t = string option
end

(** Information about the Ast, to move to lang *)
module Info : sig
  type t = private
    { range : Range.t
    ; parent : string list
    ; name : Name.t With_range.t
    ; kind : int
    ; detail : string option (* usually the type *)
    ; children : t list option
    }

  val make :
       range:Range.t
    -> parent:string list
    -> name:Name.t With_range.t
    -> kind:int
    -> ?detail:string
    -> ?children:t list
    -> unit
    -> t
end
