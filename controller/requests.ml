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
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type document_request =
  lines:string Array.t -> doc:Fleche.Doc.t -> Yojson.Safe.t

type position_request = doc:Fleche.Doc.t -> point:int * int -> Yojson.Safe.t

module Util = struct
  let asts_of_doc doc = List.filter_map Fleche.Doc.Node.ast doc.Fleche.Doc.nodes
end

open Lsp.JFleche

let symbols ~lines ~(doc : Fleche.Doc.t) =
  let uri = doc.uri in
  let f loc id =
    let name = Names.Id.to_string id in
    let kind = 12 in
    let location =
      let range = Fleche.Coq_utils.to_range ~lines loc in
      { Location.uri; range }
    in
    SymInfo.(to_yojson { name; kind; location })
  in
  let ast = Util.asts_of_doc doc in
  let slist = Coq.Ast.grab_definitions f ast in
  `List slist

let hover ~doc ~point =
  let show_loc_info = true in
  let range_span = Fleche.Info.LC.range ~doc ~point Exact in
  let range_string =
    let none fmt () = Format.fprintf fmt "no ast" in
    Format.asprintf "%a"
      (Format.pp_print_option ~none Fleche.Types.Range.pp)
      range_span
  in
  let stats = doc.stats in
  let info_string =
    Fleche.Info.LC.info ~doc ~point Exact
    |> Option.map (Fleche.Doc.Node.Info.print ~stats)
    |> Option.default "no info"
  in
  let hover_string =
    if show_loc_info then range_string ^ "\n___\n" ^ info_string
    else info_string
  in
  let contents = { HoverContents.kind = "markdown"; value = hover_string } in
  let range = range_span in
  HoverInfo.(to_yojson { contents; range })

(* Replace by ppx when we can print goals properly in the client *)
let mk_message (_loc, _lvl, msg) = msg

let mk_messages node =
  Option.map Fleche.Doc.Node.messages node
  |> Option.cata (List.map mk_message) []

let mk_error node =
  let open Fleche in
  let open Fleche.Types in
  match
    List.filter (fun d -> d.Diagnostic.severity < 2) node.Doc.Node.diags
  with
  | [] -> None
  | e :: _ -> Some e.Diagnostic.message

let goals_mode =
  if !Fleche.Config.v.goal_after_tactic then Fleche.Info.PrevIfEmpty
  else Fleche.Info.Prev

let goals ~doc ~point =
  let open Fleche in
  let goals = Info.LC.goals ~doc ~point goals_mode in
  let node = Info.LC.node ~doc ~point Exact in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  let position =
    Fleche.Types.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  Lsp.JFleche.mk_goals ~uri:doc.uri ~version:doc.version ~position ~goals
    ~messages ~error

let completion ~doc ~point:_ =
  let f _loc id = `Assoc [ ("label", `String Names.Id.(to_string id)) ] in
  let ast = Util.asts_of_doc doc in
  let clist = Coq.Ast.grab_definitions f ast in
  `List clist
