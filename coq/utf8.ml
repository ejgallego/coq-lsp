(* utf8 utils, both Coq and Camomile have similar implementations, at some point
   we should remove this but for now we keep it internal. For now we use the
   Camomille functions *)

type char = int
type index = int

(* Taken from camomille *)
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki.  *)
let rec search_head s i =
  if i >= String.length s then i
  else
    let n = Char.code (String.unsafe_get s i) in
    if n < 0x80 || n >= 0xc2 then i else search_head s (i + 1)

let next s i =
  let n = Char.code s.[i] in
  if n < 0x80 then i + 1
  else if n < 0xc0 then search_head s (i + 1)
  else if n <= 0xdf then i + 2
  else if n <= 0xef then i + 3
  else if n <= 0xf7 then i + 4
  else if n <= 0xfb then i + 5
  else if n <= 0xfd then i + 6
  else invalid_arg "UTF8.next"

let rec length_aux s c i =
  if i >= String.length s then c
  else
    let n = Char.code (String.unsafe_get s i) in
    let k =
      if n < 0x80 then 1
      else if n < 0xc0 then invalid_arg "UTF8.length"
      else if n < 0xe0 then 2
      else if n < 0xf0 then 3
      else if n < 0xf8 then 4
      else if n < 0xfc then 5
      else if n < 0xfe then 6
      else invalid_arg "UTF8.length"
    in
    length_aux s (c + 1) (i + k)

let length s = length_aux s 0 0
let rec nth_aux s i n = if n = 0 then i else nth_aux s (next s i) (n - 1)
let nth s n = nth_aux s 0 n

(* end of camomille *)

(* That's a tricky one, if the char we are requesting is out of bounds, then we
   return the last index, 0 in the case line is empty. *)
let index_of_char ~line ~char =
  if char < length line then Some (nth line char) else None

let find_char line byte =
  let rec f index n_chars =
    let next_index = next line index in
    if next_index > byte then n_chars else f next_index (n_chars + 1)
  in
  if byte < String.length line then Some (f 0 0) else None

let char_of_index ~line ~byte =
  (* if Debug.unicode then *)
  (*   Io.Log.trace "char_of_index" *)
  (*     (Format.asprintf "str: '%s' | byte: %d" line byte); *)
  let char = find_char line byte in
  (* (if Debug.unicode then *)
  (*  match char with *)
  (*  | None -> Io.Log.trace "get_last_text" "failed" *)
  (* | Some char -> Io.Log.trace "get_last_text" (Format.asprintf "char: %d"
     char)); *)
  char

(* We disabled auto-formatting in copied code *)
[@@@ocamlformat "disable=true"]

(* The following is copied from Ocaml's standard library Bytes and Uchar
   modules. We use the public safe variant of various functions, so it should be
   slower.

   TODO: when our minimum supported Ocaml version is >= 4.14 we shoud switch to
   the standard library. *)

(* From Uchar.ml *)
let rep = 0xFFFD
let decode_bits = 24
let[@inline] utf_decode n u = ((8 lor n) lsl decode_bits) lor (Uchar.to_int u)
let[@inline] utf_decode_invalid n = (n lsl decode_bits) lor rep
let[@inline] uchar_utf_decode_uchar d = Uchar.unsafe_of_int (d land 0xFFFFFF)

let uchar_utf_16_byte_length u = match Uchar.to_int u with
| u when u < 0 -> assert false
| u when u <= 0xFFFF -> 2
| u when u <= 0x10FFFF -> 4
| _ -> assert false

(* From bytes.ml *)
let[@inline] not_in_x80_to_xBF b = b lsr 6 <> 0b10
let[@inline] not_in_xA0_to_xBF b = b lsr 5 <> 0b101
let[@inline] not_in_x80_to_x9F b = b lsr 5 <> 0b100
let[@inline] not_in_x90_to_xBF b = b < 0x90 || 0xBF < b
let[@inline] not_in_x80_to_x8F b = b lsr 4 <> 0x8

let[@inline] utf_8_uchar_2 b0 b1 =
  ((b0 land 0x1F) lsl 6) lor
  ((b1 land 0x3F))

let[@inline] utf_8_uchar_3 b0 b1 b2 =
  ((b0 land 0x0F) lsl 12) lor
  ((b1 land 0x3F) lsl 6) lor
  ((b2 land 0x3F))

let[@inline] utf_8_uchar_4 b0 b1 b2 b3 =
  ((b0 land 0x07) lsl 18) lor
  ((b1 land 0x3F) lsl 12) lor
  ((b2 land 0x3F) lsl 6) lor
  ((b3 land 0x3F))

let[@inline] dec_ret n u = utf_decode n (Uchar.unsafe_of_int u)
let dec_invalid = utf_decode_invalid

let string_get_utf_8_uchar s i =
  let b = Bytes.unsafe_of_string s in
  let b0 = Bytes.get_uint8 b i in (* raises if [i] is not a valid index. *)
  let get = Bytes.get_uint8 in
  let max = Bytes.length b - 1 in
  match Char.unsafe_chr b0 with (* See The Unicode Standard, Table 3.7 *)
  | '\x00' .. '\x7F' -> dec_ret 1 b0
  | '\xC2' .. '\xDF' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_xBF b1 then dec_invalid 1 else
      dec_ret 2 (utf_8_uchar_2 b0 b1)
  | '\xE0' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_xA0_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xE1' .. '\xEC' | '\xEE' .. '\xEF' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xED' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_x9F b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      dec_ret 3 (utf_8_uchar_3 b0 b1 b2)
  | '\xF0' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x90_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      let i = i + 1 in if i > max then dec_invalid 3 else
      let b3 = get b i in if not_in_x80_to_xBF b3 then dec_invalid 3 else
      dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | '\xF1' .. '\xF3' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_xBF b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      let i = i + 1 in if i > max then dec_invalid 3 else
      let b3 = get b i in if not_in_x80_to_xBF b3 then dec_invalid 3 else
      dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | '\xF4' ->
      let i = i + 1 in if i > max then dec_invalid 1 else
      let b1 = get b i in if not_in_x80_to_x8F b1 then dec_invalid 1 else
      let i = i + 1 in if i > max then dec_invalid 2 else
      let b2 = get b i in if not_in_x80_to_xBF b2 then dec_invalid 2 else
      let i = i + 1 in if i > max then dec_invalid 3 else
      let b3 = get b i in if not_in_x80_to_xBF b3 then dec_invalid 3 else
      dec_ret 4 (utf_8_uchar_4 b0 b1 b2 b3)
  | _ -> dec_invalid 1

(* End of copy from Stdlib *)
[@@@ocamlformat "disable=false"]

let get_byte_offset_from_utf16_pos line (char : int) =
  let byte_idx = ref 0 in
  let utf16_char_count = ref 0 in
  while !byte_idx < String.length line && !utf16_char_count < char do
    let ch = string_get_utf_8_uchar line !byte_idx in
    byte_idx := next line !byte_idx;
    let code_unit_count =
      uchar_utf_16_byte_length (uchar_utf_decode_uchar ch) / 2
    in
    utf16_char_count := !utf16_char_count + code_unit_count;
    ()
  done;
  if !byte_idx < String.length line then Some !byte_idx else None

let%test_unit "utf16 offsets" =
  let testcases_x =
    [ ("aax", 2, true)
    ; ("  xoo", 2, true)
    ; ("0123", 4, false)
    ; ("  𝒞x", 4, true)
    ; ("  𝒞x𝒞", 4, true)
    ; ("  𝒞∫x", 5, true)
    ; ("  𝒞", 4, false)
    ; ("∫x.dy", 1, true)
    ]
  in
  List.iter
    (fun (s, i, b) ->
      let res = get_byte_offset_from_utf16_pos s i in
      if b then
        let res = Option.map (fun i -> s.[i]) res in
        match res with
        | Some x when x = 'x' -> ()
        | Some x ->
          failwith
            (Printf.sprintf "Didn't find x in test %s : %d, instead: %c" s i x)
        | None ->
          failwith (Printf.sprintf "Didn't not find x in test %s : %d" s i)
      else if res != None then
        failwith (Printf.sprintf "Shouldn't find x in test %s : %d" s i))
    testcases_x
