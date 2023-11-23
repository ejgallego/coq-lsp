(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type t =
  { range : Lang.Range.t
  ; contents : String.t
  }

let make ~contents ~range = { range; contents }

let delim c =
  match c with
  | '\n' | ' ' -> true
  | _ -> false

let rec find_backwards_delim offset lower text =
  if offset = lower then offset
  else if delim text.[offset - 1] then offset
  else find_backwards_delim (offset - 1) lower text

let rec id_at_point acc offset upper text =
  if delim text.[offset] || offset + 1 = upper then acc
  else id_at_point (text.[offset] :: acc) (offset + 1) upper text

let id_at_point offset upper text =
  let id = id_at_point [] offset upper text |> List.rev in
  let len = List.length id in
  String.init len (List.nth id)

let debug_find cat msg =
  if Debug.find then Io.Log.trace ("Span.find: " ^ cat) msg

let find ~offset ~(range : Lang.Range.t) text =
  let lower = range.start.offset in
  let upper = range.end_.offset in
  debug_find "lower / upper" (string_of_int lower ^ "/" ^ string_of_int upper);
  debug_find "text length" (string_of_int (String.length text));
  let rtext = String.sub text lower (upper - lower) in
  debug_find "ranged" rtext;
  debug_find "char at off" (String.make 1 text.[offset]);
  debug_find "initial offset" (string_of_int offset);
  let offset = find_backwards_delim offset lower text in
  debug_find "span.find, base offset" (string_of_int offset);
  id_at_point offset upper text
