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

  let debug_in_range = true

  let in_range ?loc (line, col) =
    (* Coq starts at 1, lsp at 0 *)
    let line = line + 1 in
    match loc with
    | None -> false
    | Some loc ->
      let Loc.
            { line_nb = line1
            ; line_nb_last = line2
            ; bol_pos
            ; bol_pos_last
            ; bp
            ; ep
            ; _
            } =
        loc
      in
      let col1 = bp - bol_pos in
      let col2 = ep - bol_pos_last in
      if debug_in_range then
        Io.Log.error "in_range"
          (Format.asprintf "(%d, %d) in (%d,%d)-(%d,%d)" line col line1 col1
             line2 col2);
      (line1 < line && line < line2)
      ||
      if line1 = line && line2 = line then col1 <= col && col < col2
      else (line1 = line && col1 <= col) || (line2 = line && col < col2)

  let gt_range ?loc:_ (_line, _pos) = false
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

  val goals :
    doc:Doc.t -> point:P.t -> approx:approx -> Coq.Goals.reified_pp option
end

module Make (P : Point) : S with module P := P = struct
  let goals ~doc ~point ~approx =
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
    find None doc.Doc.nodes |> Option.cata (fun node -> node.Doc.goal) None
end

module LC = Make (LineCol)
module O = Make (Offset)
