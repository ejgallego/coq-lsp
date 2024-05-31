(* Compatiblity and general utils *)

(* We should at some point remove all of this file in favor of a standard
   library that suits our needs *)
module Ocaml_414 : sig
  module In_channel : sig
    val with_open_bin : string -> (in_channel -> 'a) -> 'a
    val with_open_text : string -> (in_channel -> 'a) -> 'a
    val input_all : in_channel -> string
  end

  module Out_channel : sig
    val with_open : ('a -> out_channel) -> 'a -> (out_channel -> 'b) -> 'b
    val with_open_bin : string -> (out_channel -> 'a) -> 'a
  end
end

val format_to_file :
  file:string -> f:(Format.formatter -> 'a -> unit) -> 'a -> unit

module Result : sig
  include module type of Result

  module O : sig
    val ( let+ ) : ('a, 'l) t -> ('a -> 'b) -> ('b, 'l) t
    val ( let* ) : ('a, 'l) t -> ('a -> ('b, 'l) t) -> ('b, 'l) t
  end

  val split : ('a * 'b, 'e) t -> ('a, 'e) t * ('b, 'e) t

  val pp :
       (Format.formatter -> 'r -> unit)
    -> (Format.formatter -> 'e -> unit)
    -> Format.formatter
    -> ('r, 'e) Result.t
    -> unit
end
