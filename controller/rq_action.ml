(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Lsp = Fleche_lsp

let point_lt { Lang.Point.line = l1; Lang.Point.character = c1; offset = _ }
    { Lang.Point.line = l2; Lang.Point.character = c2; offset = _ } =
  l1 < l2 || (l1 = l2 && c1 < c2)

let point_gt { Lang.Point.line = l1; Lang.Point.character = c1; offset = _ }
    { Lang.Point.line = l2; Lang.Point.character = c2; offset = _ } =
  l1 > l2 || (l1 = l2 && c1 > c2)

(* To move to doc.ml *)
let filter_map_range ~range ~nodes ~f =
  let rec aux (nodes : Fleche.Doc.Node.t list) acc =
    match nodes with
    | [] -> List.rev acc
    | node :: nodes -> (
      let open Lang.Range in
      let nrange = node.range in
      if point_lt nrange.end_ range.start then aux nodes acc
      else if point_gt nrange.start range.end_ then List.rev acc
      else
        (* Node in scope *)
        match f node with
        | Some res -> aux nodes (res :: acc)
        | None -> aux nodes acc)
  in
  aux nodes []

(* util *)
let filter_map_cut f l =
  match List.filter_map f l with
  | [] -> None
  | res -> Some res

(* Return list of pairs of diags, qf *)
let get_qf (d : Lang.Diagnostic.t) : _ option =
  Option.bind d.data (function
    | { Lang.Diagnostic.Data.quickFix = Some qf; _ } -> Some (d, qf)
    | _ -> None)

let get_qfs ~range (doc : Fleche.Doc.t) =
  let f { Fleche.Doc.Node.diags; _ } = filter_map_cut get_qf diags in
  filter_map_range ~range ~nodes:doc.nodes ~f |> List.concat

let request ~range ~token:_ ~(doc : Fleche.Doc.t) =
  let kind = Some "quickfix" in
  let isPreferred = Some true in
  let qf = get_qfs ~range doc in
  let bf (d, qf) =
    List.map
      (fun { Lang.Qf.range; newText } ->
        let oldText =
          Fleche.Contents.extract_raw ~contents:doc.contents ~range
        in
        let title = Format.asprintf "Replace `%s` by `%s`" oldText newText in
        let diagnostics = [ d ] in
        let qf = [ Lsp.Workspace.TextEdit.{ range; newText } ] in
        let changes = [ (doc.uri, qf) ] in
        let edit = Some Lsp.Workspace.WorkspaceEdit.{ changes } in
        Lsp.Core.CodeAction.{ title; kind; diagnostics; isPreferred; edit })
      qf
  in
  List.concat_map bf qf

let request ~range ~token ~(doc : Fleche.Doc.t) =
  let res = request ~range ~token ~doc in
  Ok (`List (List.map Lsp.Core.CodeAction.to_yojson res))
