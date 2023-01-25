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
let byte_of_char ~line ~char = nth line char

let find_char line byte =
  let rec f index n_chars =
    let next_index = next line index in
    if next_index > byte then n_chars else f next_index (n_chars + 1)
  in
  if String.length line <= byte then length line else f 0 0

let char_of_byte ~line ~byte =
  if Debug.unicode then
    Io.Log.trace "get_last_text"
      (Format.asprintf "str: '%s' | byte: %d" line byte);
  let res = find_char line byte in
  if Debug.unicode then
    Io.Log.trace "get_last_text" (Format.asprintf "char: %d" res);
  res
