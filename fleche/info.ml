(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright (C) 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+  *)
(* Copyright (C) 2019-2022 Emilio J. Gallego Arias, INRIA               *)
(* Copyright (C) 2022-2022 Shachar Itzhaky, Technion                    *)
(************************************************************************)

module type Point = sig
  type t

  val in_range : ?range:Lang.Range.t -> t -> bool
  val gt_range : ?range:Lang.Range.t -> t -> bool

  type offset_table = string

  val to_offset : t -> offset_table -> int
  val to_string : t -> string
end

module LineCol : Point with type t = int * int = struct
  type t = int * int
  type offset_table = string

  let line_length offset text =
    match String.index_from_opt text offset '\n' with
    | Some l -> l - offset
    | None -> String.length text - offset

  let rec to_offset cur lc (l, c) text =
    Io.Log.trace "to_offset"
      (Format.asprintf "cur: %d | lc: %d | l: %d c: %d" cur lc l c);
    if lc = l then cur + c
    else
      let ll = line_length cur text + 1 in
      to_offset (cur + ll) (lc + 1) (l, c) text

  let to_offset (l, c) text = to_offset 0 0 (l, c) text
  let to_string (l, c) = "(" ^ string_of_int l ^ "," ^ string_of_int c ^ ")"
  let debug_in_range = false

  let debug_in_range hdr line col line1 col1 line2 col2 =
    if debug_in_range then
      Io.Log.trace hdr
        (Format.asprintf "(%d, %d) in (%d,%d)-(%d,%d)" line col line1 col1 line2
           col2)

  let in_range ?range (line, col) =
    (* Coq starts at 1, lsp at 0 *)
    match range with
    | None -> false
    | Some r ->
      let line1 = r.Lang.Range.start.line in
      let col1 = r.start.character in
      let line2 = r.end_.line in
      let col2 = r.end_.character in
      debug_in_range "in_range" line col line1 col1 line2 col2;
      (line1 < line && line < line2)
      ||
      if line1 = line && line2 = line then col1 <= col && col < col2
      else (line1 = line && col1 <= col) || (line2 = line && col < col2)

  let gt_range ?range (line, col) =
    match range with
    | None -> false
    | Some r ->
      let line1 = r.Lang.Range.start.line in
      let col1 = r.start.character in
      let line2 = r.end_.line in
      let col2 = r.end_.character in
      debug_in_range "gt_range" line col line1 col1 line2 col2;
      line < line1 || (line = line1 && col < col1)
end

module Offset : Point with type t = int = struct
  type t = int
  type offset_table = string

  let in_range ?range point =
    match range with
    | None -> false
    | Some range ->
      range.Lang.Range.start.offset <= point
      && point < range.Lang.Range.end_.offset

  let gt_range ?range point =
    match range with
    | None -> false
    | Some range -> point < range.Lang.Range.start.offset

  let to_offset off _ = off
  let to_string off = string_of_int off
end

type approx =
  | Exact
  (* Exact on point *)
  | PrevIfEmpty
  (* If no match, return prev *)
  | Prev

module type S = sig
  module P : Point

  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  val node : (approx, Doc.Node.t) query
end

let some x = Some x

module Make (P : Point) : S with module P := P = struct
  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  let find ~doc ~point approx =
    let rec find prev l =
      match l with
      | [] -> prev
      | node :: xs -> (
        let range = node.Doc.Node.range in
        match approx with
        | Exact -> if P.in_range ~range point then Some node else find None xs
        | PrevIfEmpty ->
          if P.gt_range ~range point then prev else find (Some node) xs
        | Prev ->
          if P.gt_range ~range point || P.in_range ~range point then prev
          else find (Some node) xs)
    in
    find None doc.Doc.nodes

  let node = find
end

module LC = Make (LineCol)
module O = Make (Offset)

(* XXX: We need to split this module in two: one that handles the extraction of
   information from a document, and the other that further processes it, like
   for goals, possibly executing Coq code. *)

(* Related to goal request *)
module Goals = struct
  let pr_goal st =
    let ppx env sigma x =
      let { Coq.Protect.E.r; feedback } =
        Coq.Print.pr_letype_env ~goal_concl_style:true env sigma x
      in
      (* XXX: We ideally want to thread this in the monad too, but it'd be
         better if the printer was more functional *)
      Io.Log.feedback feedback;
      match r with
      | Coq.Protect.R.Completed (Ok pr) -> pr
      | Coq.Protect.R.Completed (Error _pr) -> Pp.str "printer failed!"
      | Interrupted -> Pp.str "printer interrupted!"
    in
    let lemmas = Coq.State.lemmas ~st in
    Option.map (Coq.Goals.reify ~ppx) lemmas

  (* We need to use [in_state] here due to printing not being pure, but we want
     a better design here eventually *)
  let goals ~st = Coq.State.in_state ~st ~f:pr_goal st
  let program ~st = Coq.State.program ~st
end

module Completion = struct
  (* XXX: This belongs in Coq *)
  let pr_extref gr =
    match gr with
    | Globnames.TrueGlobal gr -> Printer.pr_global gr
    | Globnames.Abbrev kn -> Names.KerName.print kn

  (* XXX This may fail when passed "foo." for example, so more sanitizing is
     needed *)
  let to_qualid p = try Some (Libnames.qualid_of_string p) with _ -> None

  let candidates ~st prefix =
    let ( let* ) = Option.bind in
    Coq.State.in_state ~st prefix ~f:(fun prefix ->
        let* p = to_qualid prefix in
        Nametab.completion_canditates p
        |> List.map (fun x -> Pp.string_of_ppcmds (pr_extref x))
        |> some)
end
