val input_all : string -> string

val format_to_file :
  file:string -> f:(Format.formatter -> 'a -> unit) -> 'a -> unit
