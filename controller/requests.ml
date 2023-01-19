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

let mk_syminfo file (name, _path, kind, range) : Yojson.Safe.t =
  `Assoc
    [ ("name", `String name)
    ; ("kind", `Int kind)
    ; (* function *)
      ( "location"
      , `Assoc [ ("uri", `String file); ("range", Lsp.Base.mk_range range) ] )
    ]

let symbols ~lines ~(doc : Fleche.Doc.t) =
  let uri = doc.uri in
  let f loc id =
    let range = Fleche.Coq_utils.to_range ~lines loc in
    mk_syminfo uri (Names.Id.to_string id, "", 12, range)
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
  `Assoc
    ([ ( "contents"
       , `Assoc
           [ ("kind", `String "markdown"); ("value", `String hover_string) ] )
     ]
    @ Option.cata
        (fun range -> [ ("range", Lsp.Base.mk_range range) ])
        [] range_span)

(* Replace by ppx when we can print goals properly in the client *)
let mk_hyp { Coq.Goals.names; def = _; ty } : Yojson.Safe.t =
  let names = List.map (fun id -> `String (Names.Id.to_string id)) names in
  let ty = Pp.string_of_ppcmds ty in
  `Assoc [ ("names", `List names); ("ty", `String ty) ]

let mk_goal { Coq.Goals.info = _; ty; hyps } : Yojson.Safe.t =
  let ty = Pp.string_of_ppcmds ty in
  `Assoc [ ("ty", `String ty); ("hyps", `List (List.map mk_hyp hyps)) ]

let mk_goals { Coq.Goals.goals; stack = _; bullet = _; shelf; given_up } =
  `Assoc
    [ ("goals", `List (List.map mk_goal goals))
    ; ("stack", `Null)
    ; ("bullet", `Null)
    ; ("shelf", `List (List.map mk_goal shelf))
    ; ("given_up", `List (List.map mk_goal given_up))
    ]

let mk_goals = Option.cata mk_goals `Null
let mk_message (_loc, _lvl, msg) = `String (Pp.string_of_ppcmds msg)
let mk_messages m = List.map mk_message m
let mk_messages = Option.cata mk_messages []

let mk_error node =
  let open Fleche in
  let open Fleche.Types in
  match
    List.filter (fun d -> d.Diagnostic.severity < 2) node.Doc.Node.diags
  with
  | [] -> []
  | e :: _ -> [ ("error", `String e.Diagnostic.message) ]

let goals_mode =
  if !Fleche.Config.v.goal_after_tactic then Fleche.Info.PrevIfEmpty
  else Fleche.Info.Prev

let goals ~doc ~point =
  let open Fleche in
  let goals = Info.LC.goals ~doc ~point goals_mode in
  let node = Info.LC.node ~doc ~point Exact in
  let messages = Option.map Doc.Node.messages node in
  let error = Option.cata mk_error [] node in
  `Assoc
    ([ ( "textDocument"
       , `Assoc [ ("uri", `String doc.uri); ("version", `Int doc.version) ] )
     ; ( "position"
       , `Assoc [ ("line", `Int (fst point)); ("character", `Int (snd point)) ]
       )
     ; ("goals", mk_goals goals)
     ; ("messages", `List (mk_messages messages))
     ]
    @ error)

let completion ~doc ~point:_ =
  let f _loc id = `Assoc [ ("label", `String Names.Id.(to_string id)) ] in
  let ast = Util.asts_of_doc doc in
  let clist = Coq.Ast.grab_definitions f ast in
  `List clist
