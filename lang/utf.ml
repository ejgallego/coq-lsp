(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* LICENSE NOTE: this file includes code from camomille and OCaml stdlib (for
   compatibilty). This is just out of convenience, the included functions are
   quite trivial, and eventually we should be able to use OCaml's stdlib and
   remove most of this code. *)

(* Camomille Copyright: *)
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(** This module provides facilities for translating language-based locations to
    protocol-based locations.

    After a long discussion (thanks Léo !), we have decided that the best is to
    have `Lang.Point` to store columns offset in the values that are native to
    the protocol under consideration, set by the upper layers.

    This scheme kind of follows what we have done since the start with coq-lsp. *)
module Encoding = struct
  (* Used for char offsets *)
  type t =
    | Utf8
    | Utf16
    | Utf32
end

(* Future work: support multiple encondings *)
(* val set_protocol_encoding : *)

(* EJGA: Taken from Camomille, but note what I wrote below *)

(* utf8 utils, both Coq and Camomile have similar implementations, at some point
   we should remove this but for now we keep it internal. For now we use the
   Camomille functions *)

type utf8_string = string
type char = int
type utf8_index = int
type utf16_index = int

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

let length_utf16 line =
  let byte_idx = ref 0 in
  let utf16_len = ref 0 in
  let len = String.length line in
  while !byte_idx < len do
    let ch = string_get_utf_8_uchar line !byte_idx in
    let next_idx = next line !byte_idx in
    byte_idx := next_idx;
    let l = uchar_utf_16_byte_length (uchar_utf_decode_uchar ch) / 2 in
    utf16_len := !utf16_len + l
  done;
  !utf16_len

(* UTF16 <-> UTF8 *)

let utf8_offset_of_utf16_offset ~line ~(offset : utf16_index) =
  let byte_idx = ref 0 in
  let utf16_char_count = ref 0 in
  let len = String.length line in
  (try
     while !utf16_char_count < offset do
       let ch = string_get_utf_8_uchar line !byte_idx in
       let next_idx = next line !byte_idx in
       if next_idx >= len then raise Not_found else byte_idx := next_idx;
       let code_unit_count =
         uchar_utf_16_byte_length (uchar_utf_decode_uchar ch) / 2
       in
       utf16_char_count := !utf16_char_count + code_unit_count;
       ()
     done
   with _ -> ());
  !byte_idx

let utf16_offset_of_utf8_offset ~line ~(offset : utf8_index) =
  let byte_idx = ref 0 in
  let utf16_char_count = ref 0 in
  let len = String.length line in
  (try
     while !byte_idx < offset do
       let ch = string_get_utf_8_uchar line !byte_idx in
       let next_idx = next line !byte_idx in
       if next_idx > len then raise Not_found else byte_idx := next_idx;
       let code_unit_count =
         uchar_utf_16_byte_length (uchar_utf_decode_uchar ch) / 2
       in
       utf16_char_count := !utf16_char_count + code_unit_count;
       ()
     done
   with _ -> ());
  !utf16_char_count

(******************************************************)
(** Not used anywhere, remove? *)
(******************************************************)

(* UTF16 <-> Char *)
let char_of_utf16_offset ~line ~(offset : utf16_index) =
  let byte_idx = ref 0 in
  let count = ref 0 in
  let utf16_char_count = ref 0 in
  let len = String.length line in
  (try
     while !utf16_char_count < offset do
       let ch = string_get_utf_8_uchar line !byte_idx in
       let next_idx = next line !byte_idx in
       if next_idx >= len then raise Not_found else byte_idx := next_idx;
       let code_unit_count =
         uchar_utf_16_byte_length (uchar_utf_decode_uchar ch) / 2
       in
       utf16_char_count := !utf16_char_count + code_unit_count;
       count := !count + 1;
       ()
     done
   with _ -> ());
  !count

let utf16_offset_of_char ~line ~(char : char) =
  let offset16 = ref 0 in
  let idx = ref 0 in
  for _ = 0 to char - 1 do
    let ch = string_get_utf_8_uchar line !idx in
    let byte_len = uchar_utf_16_byte_length (uchar_utf_decode_uchar ch) in
    offset16 := !offset16 + (byte_len / 2);
    idx := next line !idx
  done;
  !offset16

(* UTF8 <-> Char *)

(* That's a tricky one, if the char we are requesting is out of bounds, then we
   return the last index, 0 in the case line is empty. *)
let utf8_offset_of_char ~line ~char =
  if char < length line then Some (nth line char) else None

let find_char line byte =
  let rec f index n_chars =
    let next_index = next line index in
    if next_index > byte then n_chars else f next_index (n_chars + 1)
  in
  if byte < String.length line then Some (f 0 0) else None

let char_of_utf8_offset ~line ~offset =
  (* if Debug.unicode then *)
  (*   Io.Log.trace "char_of_index" *)
  (*     (Format.asprintf "str: '%s' | byte: %d" line byte); *)
  let char = find_char line offset in
  (* (if Debug.unicode then *)
  (*  match char with *)
  (*  | None -> Io.Log.trace "get_last_text" "failed" *)
  (* | Some char -> Io.Log.trace "get_last_text" (Format.asprintf "char: %d"
     char)); *)
  char
