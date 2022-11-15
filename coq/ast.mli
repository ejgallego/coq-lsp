type t

(* Single identifier *)
module Id : sig
  type t

  val to_string : t -> string
end

(* Qualified Identifier *)
module QualId : sig
  type t
end

(* Comparison / hash functions *)
val hash : t -> int
val compare : t -> t -> int
val loc : t -> Loc.t option
val print : t -> Pp.t
val grab_definitions : (Loc.t -> Id.t -> 'a) -> t list -> 'a list
val marshal_in : in_channel -> t
val marshal_out : out_channel -> t -> unit

(* Analysis on AST / Structure inference *)
module View : sig
  type ast = t

  type t =
    (* This could be also extracted from the interpretation *)
    | Open of unit
    | End of unit
    | Require of
        { prefix : QualId.t option
        ; refs : QualId.t list
        }
    | Other

  val kind : ast -> t
end

(* This can't be used outside of the [Coq] library, and will be gone once we
   functiorialize the interface *)
module Internal : sig
  val to_coq : t -> Vernacexpr.vernac_control
  val of_coq : Vernacexpr.vernac_control -> t
end
