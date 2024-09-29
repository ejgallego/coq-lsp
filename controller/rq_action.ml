let dqf (d : Lang.Diagnostic.t) : _ option =
  Option.bind d.data (function
    | { Lang.Diagnostic.Data.quickFix = Some qf; _ } -> Some (d, qf)
    | _ -> None)

let point_lt { Lang.Point.line = l1; Lang.Point.character = c1; offset = _ }
    { Lang.Point.line = l2; Lang.Point.character = c2; offset = _ } =
  l1 < l2 || (l1 = l2 && c1 < c2)

let point_gt { Lang.Point.line = l1; Lang.Point.character = c1; offset = _ }
    { Lang.Point.line = l2; Lang.Point.character = c2; offset = _ } =
  l1 > l2 || (l1 = l2 && c1 > c2)

let get_qf ~range (doc : Fleche.Doc.t) =
  let diags =
    List.filter_map
      (fun (node : Fleche.Doc.Node.t) ->
        let open Lang.Range in
        (* let open Lang.Point in *)
        let nrange = node.range in
        if point_lt nrange.end_ range.start || point_gt nrange.start range.end_
        then None
        else Some node.diags)
      doc.nodes
    |> List.concat
  in
  List.filter_map dqf diags

let request ~range ~token:_ ~(doc : Fleche.Doc.t) =
  let kind = Some "quickfix" in
  let isPreferred = Some true in
  let qf = get_qf ~range doc in
  let bf (d, qf) =
    let mm =
      match qf with
      | [ q ] -> q.Lang.Qf.newText
      | _ -> "correct code"
    in
    let title = "Replace with " ^ mm in
    let diagnostics = [ d ] in
    let qff { Lang.Qf.range; newText } =
      Lsp.Workspace.TextEdit.{ range; newText }
    in
    let changes = [ (doc.uri, List.map qff qf) ] in
    let edit = Some Lsp.Workspace.WorkspaceEdit.{ changes } in
    Lsp.Core.CodeAction.{ title; kind; diagnostics; isPreferred; edit }
  in
  List.map bf qf

let request ~range ~token ~(doc : Fleche.Doc.t) =
  let res = request ~range ~token ~doc in
  Ok (`List (List.map Lsp.Core.CodeAction.to_yojson res))
