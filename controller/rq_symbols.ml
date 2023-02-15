(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let rec mk_syminfo info =
  let Coq.Ast.Info.{ range; name; kind; detail; children } = info in
  let { CAst.loc = _name_loc; v = name } = name in
  let name = Names.Name.print name |> Pp.string_of_ppcmds in
  let children = Option.map (List.map mk_syminfo) children in
  let selectionRange = range in
  (* Need to fix this at coq.ast level *)
  (* let selectionRange = Option.get name_loc in *)
  Lsp.JFleche.DocumentSymbol.
    { name
    ; kind
    ; detail
    ; tags = None
    ; deprecated = None
    ; range
    ; selectionRange
    ; children
    }

let mk_syminfo info = mk_syminfo info |> Lsp.JFleche.DocumentSymbol.to_yojson
let definition_info { Fleche.Doc.Node.Ast.ast_info; _ } = ast_info

let symbols ~(doc : Fleche.Doc.t) =
  let definfo =
    Fleche.Doc.asts doc |> List.filter_map definition_info |> List.concat
  in
  let result = List.map mk_syminfo definfo in
  `List result
