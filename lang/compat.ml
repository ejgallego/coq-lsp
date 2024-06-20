(* OCaml compat *)

(* The following is copied from Ocaml's standard library Bytes and Uchar
   modules. We use the public safe variant of various functions, so it should be
   slower.

   TODO: when our minimum supported Ocaml version is >= 4.14 we shoud switch to
   the standard library. *)
module Uchar_ = Uchar

module OCaml4_14 = struct
  module Uchar = struct
    type utf_decode = int

    (* From Uchar.ml *)
    let rep = 0xFFFD
    let valid_bit = 27
    let decode_bits = 24
    let[@inline] utf_decode_is_valid d = d lsr valid_bit = 1
    let[@inline] utf_decode_length d = (d lsr decode_bits) land 0b111
    let[@inline] utf_decode_uchar d = Uchar.unsafe_of_int (d land 0xFFFFFF)
    let[@inline] utf_decode n u = ((8 lor n) lsl decode_bits) lor Uchar.to_int u
    let[@inline] utf_decode_invalid n = (n lsl decode_bits) lor rep

    let utf_8_byte_length u =
      match Uchar.to_int u with
      | u when u < 0 -> assert false
      | u when u <= 0x007F -> 1
      | u when u <= 0x07FF -> 2
      | u when u <= 0xFFFF -> 3
      | u when u <= 0x10FFFF -> 4
      | _ -> assert false

    let utf_16_byte_length u =
      match Uchar.to_int u with
      | u when u < 0 -> assert false
      | u when u <= 0xFFFF -> 2
      | u when u <= 0x10FFFF -> 4
      | _ -> assert false
  end

  module String = struct
    let[@inline] not_in_x80_to_xBF b = b lsr 6 <> 0b10
    let[@inline] not_in_xA0_to_xBF b = b lsr 5 <> 0b101
    let[@inline] not_in_x80_to_x9F b = b lsr 5 <> 0b100
    let[@inline] not_in_x90_to_xBF b = b < 0x90 || 0xBF < b
    let[@inline] not_in_x80_to_x8F b = b lsr 4 <> 0x8
    let[@inline] utf_8_uchar_2 b0 b1 = ((b0 land 0x1F) lsl 6) lor (b1 land 0x3F)

    let[@inline] utf_8_uchar_3 b0 b1 b2 =
      ((b0 land 0x0F) lsl 12) lor ((b1 land 0x3F) lsl 6) lor (b2 land 0x3F)

    let[@inline] utf_8_uchar_4 b0 b1 b2 b3 =
      ((b0 land 0x07) lsl 18)
      lor ((b1 land 0x3F) lsl 12)
      lor ((b2 land 0x3F) lsl 6)
      lor (b3 land 0x3F)

    let[@inline] dec_ret n u = Uchar.utf_decode n (Uchar_.unsafe_of_int u)
    let dec_invalid = Uchar.utf_decode_invalid

    let get_utf_8_uchar s i =
      let b = Bytes.unsafe_of_string s in
      let b0 = Bytes.get_uint8 b i in
      (* raises if [i] is not a valid index. *)
      let get = Bytes.get_uint8 in
      let max = Bytes.length b - 1 in
      match Char.unsafe_chr b0 with
      (* See The Unicode Standard, Table 3.7 *)
      | '\x00' .. '\x7F' -> dec_ret 1 b0
      | '\xC2' .. '\xDF' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_x80_to_xBF b1 then dec_invalid 1
          else dec_ret 2 (utf_8_uchar_2 b0 b1)
      | '\xE0' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_xA0_to_xBF b1 then dec_invalid 1
          else
            let i = i + 1 in
            if i > max then dec_invalid 2
            else
              let b2 = get b i in
              if not_in_x80_to_xBF b2 then dec_invalid 2
              else dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
      | '\xE1' .. '\xEC' | '\xEE' .. '\xEF' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_x80_to_xBF b1 then dec_invalid 1
          else
            let i = i + 1 in
            if i > max then dec_invalid 2
            else
              let b2 = get b i in
              if not_in_x80_to_xBF b2 then dec_invalid 2
              else dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
      | '\xED' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_x80_to_x9F b1 then dec_invalid 1
          else
            let i = i + 1 in
            if i > max then dec_invalid 2
            else
              let b2 = get b i in
              if not_in_x80_to_xBF b2 then dec_invalid 2
              else dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
      | '\xF0' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_x90_to_xBF b1 then dec_invalid 1
          else
            let i = i + 1 in
            if i > max then dec_invalid 2
            else
              let b2 = get b i in
              if not_in_x80_to_xBF b2 then dec_invalid 2
              else
                let i = i + 1 in
                if i > max then dec_invalid 3
                else
                  let b3 = get b i in
                  if not_in_x80_to_xBF b3 then dec_invalid 3
                  else dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
      | '\xF1' .. '\xF3' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_x80_to_xBF b1 then dec_invalid 1
          else
            let i = i + 1 in
            if i > max then dec_invalid 2
            else
              let b2 = get b i in
              if not_in_x80_to_xBF b2 then dec_invalid 2
              else
                let i = i + 1 in
                if i > max then dec_invalid 3
                else
                  let b3 = get b i in
                  if not_in_x80_to_xBF b3 then dec_invalid 3
                  else dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
      | '\xF4' ->
        let i = i + 1 in
        if i > max then dec_invalid 1
        else
          let b1 = get b i in
          if not_in_x80_to_x8F b1 then dec_invalid 1
          else
            let i = i + 1 in
            if i > max then dec_invalid 2
            else
              let b2 = get b i in
              if not_in_x80_to_xBF b2 then dec_invalid 2
              else
                let i = i + 1 in
                if i > max then dec_invalid 3
                else
                  let b3 = get b i in
                  if not_in_x80_to_xBF b3 then dec_invalid 3
                  else dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
      | _ -> dec_invalid 1
  end
end
