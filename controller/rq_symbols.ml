(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let rec mk_syminfo ~lines info =
  let Coq.Ast.Info.{ range; name; kind; detail; children } = info in
  let range = Fleche.Coq_utils.to_range ~lines range in
  let { CAst.loc = name_loc; v = name } = name in
  let selectionRange = Fleche.Coq_utils.to_range ~lines (Option.get name_loc) in
  let name = Names.Name.print name |> Pp.string_of_ppcmds in
  let children = Option.map (List.map (mk_syminfo ~lines)) children in
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

let mk_syminfo ~lines info =
  mk_syminfo ~lines info |> Lsp.JFleche.DocumentSymbol.to_yojson

let definition_info { Fleche.Doc.Node.Ast.ast_info; _ } = ast_info

let symbols ~lines ~(doc : Fleche.Doc.t) =
  let definfo =
    Fleche.Doc.asts doc |> List.filter_map definition_info |> List.concat
  in
  let result = List.map (mk_syminfo ~lines) definfo in
  `List result
