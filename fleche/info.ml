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

  val in_range : ?loc:Loc.t -> t -> bool
  val gt_range : ?loc:Loc.t -> t -> bool
end

module LineCol : Point with type t = int * int = struct
  type t = int * int

  let debug_in_range = false

  let in_range ?loc (line, col) =
    (* Coq starts at 1, lsp at 0 *)
    match loc with
    | None -> false
    | Some loc ->
      let r = Types.to_range loc in
      let line1 = r.start.line in
      let col1 = r.start.character in
      let line2 = r._end.line in
      let col2 = r._end.character in
      if debug_in_range then
        Io.Log.error "in_range"
          (Format.asprintf "(%d, %d) in (%d,%d)-(%d,%d)" line col line1 col1
             line2 col2);
      (line1 < line && line < line2)
      ||
      if line1 = line && line2 = line then col1 <= col && col < col2
      else (line1 = line && col1 <= col) || (line2 = line && col < col2)

  let gt_range ?loc (line, col) =
    match loc with
    | None -> false
    | Some loc ->
      let r = Types.to_range loc in
      let line1 = r.start.line in
      let col1 = r.start.character in
      let line2 = r._end.line in
      let col2 = r._end.character in
      if debug_in_range then
        Io.Log.error "gt_range"
          (Format.asprintf "(%d, %d) in (%d,%d)-(%d,%d)" line col line1 col1
             line2 col2);
      line2 < line || (line2 = line && col2 <= col)
end

module Offset : Point with type t = int = struct
  type t = int

  let in_range ?loc point =
    match loc with
    | None -> false
    | Some loc -> loc.Loc.bp <= point && point < loc.ep

  let gt_range ?loc point =
    match loc with
    | None -> false
    | Some loc -> point < loc.Loc.bp
end

type approx =
  | Exact
  | PickPrev

module type S = sig
  module P : Point

  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  val goals : (approx, Coq.Goals.reified_pp) query
  val completion : (string, string list) query
end

let some x = Some x
let obind x f = Option.bind f x

module Make (P : Point) : S with module P := P = struct
  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  let find ~doc ~point approx =
    let rec find prev l =
      match l with
      | [] -> prev
      | node :: xs -> (
        let loc = Coq.Ast.loc node.Doc.ast in
        match approx with
        | Exact -> if P.in_range ?loc point then Some node else find None xs
        | PickPrev ->
          if P.gt_range ?loc point then prev else find (Some node) xs)
    in
    find None doc.Doc.nodes

  let goals ~doc ~point approx =
    find ~doc ~point approx |> obind (fun node -> node.Doc.goal)

  (* XXX: This belongs in Coq *)
  let pr_extref gr =
    match gr with
    | Globnames.TrueGlobal gr -> Printer.pr_global gr
    | Globnames.Abbrev kn -> Names.KerName.print kn

  (* XXX This may fail when passed "foo." for example, so more sanitizing is
     needed *)
  let to_qualid p = try Some (Libnames.qualid_of_string p) with _ -> None

  let completion ~doc ~point prefix =
    find ~doc ~point Exact
    |> obind (fun node ->
           Coq.State.in_state ~st:node.Doc.state prefix ~f:(fun prefix ->
               to_qualid prefix
               |> obind (fun p ->
                      Nametab.completion_canditates p
                      |> List.map (fun x -> Pp.string_of_ppcmds (pr_extref x))
                      |> some)))
end

module LC = Make (LineCol)
module O = Make (Offset)
