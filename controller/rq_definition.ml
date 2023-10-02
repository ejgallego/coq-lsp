(************************************************************************)
(* Coq Language Server Protocol -- Jump to definition                   *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let request ~(doc : Fleche.Doc.t) ~point =
  let { Fleche.Doc.contents; _ } = doc in
  Option.cata
    (fun id_at_point ->
      let { Fleche.Doc.toc; _ } = doc in
      match CString.Map.find_opt id_at_point toc with
      | Some range ->
        let uri = doc.uri in
        Lsp.Core.Location.({ uri; range } |> to_yojson)
      | None -> `Null)
    `Null
    (Rq_common.get_id_at_point ~contents ~point)
  |> Result.ok
