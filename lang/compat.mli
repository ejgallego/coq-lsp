module OCaml4_14 : sig
  module Uchar : sig
    type utf_decode

    val utf_decode_is_valid : utf_decode -> bool
    val utf_decode_uchar : utf_decode -> Uchar.t
    val utf_decode_length : utf_decode -> int
    val utf_decode : int -> Uchar.t -> int
    val utf_8_byte_length : Uchar.t -> int
    val utf_16_byte_length : Uchar.t -> int
  end

  module String : sig
    val get_utf_8_uchar : string -> int -> Uchar.utf_decode
  end
end
