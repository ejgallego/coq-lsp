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

module G = Serapi.Serapi_goals

let in_range ?loc (line, pos) =
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
    (line1 - 1 < line && line < line2 - 1)
    || (line1 - 1 = line && col1 <= pos)
    || (line2 - 1 = line && pos <= col2)

let gt_range ?loc:_ (_line, _pos) = false

let in_range_point ?loc point =
  match loc with
  | None -> false
  | Some loc -> loc.Loc.bp <= point && point < loc.ep

let gt_range_point ?loc point =
  match loc with
  | None -> false
  | Some loc -> point < loc.Loc.bp

type approx =
  | Exact
  | PickPrev

let get_goals ~in_range ~gt_range ~doc ~point ~approx =
  let rec find prev l =
    match l with
    | [] -> prev
    | node :: xs -> (
      let loc = Coq.Ast.loc node.Doc.ast in
      match approx with
      | Exact -> if in_range ?loc point then Some node else find (Some node) xs
      | PickPrev -> if gt_range ?loc point then prev else find (Some node) xs)
  in
  find None doc.Doc.nodes |> Option.cata (fun node -> node.Doc.goal) None

let get_goals_line_col ~doc ~point =
  get_goals ~in_range ~gt_range ~doc ~point ~approx:Exact

let get_goals_point ~doc ~point ~approx =
  get_goals ~in_range:in_range_point ~gt_range:gt_range_point ~doc ~point
    ~approx
