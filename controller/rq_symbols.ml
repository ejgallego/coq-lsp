(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let rec mk_syminfo info =
  let Lang.Ast.Info.{ range; parent; name; kind; detail; children } = info in
  let { Lang.With_range.range = selectionRange; v = name } = name in
  let name = Option.default "_" name in
  (* Doesn't look so nice yet *)
  (* let name = String.concat " > " (List.rev (name :: parent)) in *)
  let children = Option.map (List.map mk_syminfo) children in
  (* Need to fix this at coq.ast level *)
  (* let selectionRange = Option.get name_loc in *)
  Lsp.Core.DocumentSymbol.
    { name
    ; kind
    ; detail
    ; tags = None
    ; deprecated = None
    ; range
    ; selectionRange
    ; children
    }

let mk_syminfo info = mk_syminfo info |> Lsp.Core.DocumentSymbol.to_yojson
let definition_info { Fleche.Doc.Node.Ast.ast_info; _ } = ast_info

let symbols ~token:_ ~(doc : Fleche.Doc.t) =
  let definfo =
    Fleche.Doc.asts doc |> List.filter_map definition_info |> List.concat
  in
  let result = List.map mk_syminfo definfo in
  `List result |> Result.ok
