type t

val loc : t -> Loc.t option
val hash : t -> int
val compare : t -> t -> int
val grab_definitions : (Loc.t -> Names.Id.t -> 'a) -> t list -> 'a list

(** Printing *)
val print : t -> Pp.t

val pp_loc : ?print_file:bool -> Format.formatter -> Loc.t -> unit
val loc_to_string : ?print_file:bool -> Loc.t -> string

(** Unused for now *)
val marshal_in : in_channel -> t

val marshal_out : out_channel -> t -> unit

(** Internal, will go away once the [Lang.t] interface is ready *)
val to_coq : t -> Vernacexpr.vernac_control

val of_coq : Vernacexpr.vernac_control -> t
