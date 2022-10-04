(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type t =
  { range : Types.Range.t
  ; text : String.t
  }

let make ~contents ~loc =
  let range = Types.to_range loc in
  let len = loc.Loc.ep - loc.Loc.bp in
  let text = String.sub contents loc.Loc.bp len in
  Io.Log.error "get_segment" text;
  { range; text }

let rec find_backwards_delim offset text =
  if offset = 0 then 0
  else if text.[offset] = ' ' then offset
  else find_backwards_delim (offset - 1) text

let rec id_at_point acc offset text =
  if text.[offset] = ' ' then acc
  else id_at_point (text.[offset] :: acc) (offset + 1) text

let id_at_point offset text =
  let id = id_at_point [] offset text |> List.rev in
  let len = List.length id in
  String.init len (List.nth id)

let find ~offset { range; text } =
  let offset = offset - range.start.offset in
  let offset = find_backwards_delim offset text in
  id_at_point offset text
