type t

val loc : t -> Loc.t option

val hash : t -> int
val compare : t -> t -> int

val to_coq : t -> Vernacexpr.vernac_control
val of_coq : Vernacexpr.vernac_control -> t

val print : t -> Pp.t

val grab_definitions : (Loc.t -> Names.Id.t -> 'a) -> t list -> 'a list

val marshal_in : in_channel -> t
val marshal_out : out_channel -> t -> unit
