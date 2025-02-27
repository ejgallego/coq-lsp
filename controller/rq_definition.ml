(************************************************************************)
(* Coq Language Server Protocol -- Jump to definition                   *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Fleche_lsp.Core

let get_from_toc ~doc id_at_point =
  let { Fleche.Doc.toc; _ } = doc in
  Fleche.Io.Log.trace "rq_definition" "get_from_toc";
  match CString.Map.find_opt id_at_point toc with
  | Some node ->
    let uri = doc.uri in
    let range = node.range in
    Some Location.{ uri; range }
  | None -> None

let lp_to_string exn = CErrors.iprint exn |> Pp.string_of_ppcmds
let err_code = -32803

let locate_extended qid =
  try Some (Nametab.locate_extended qid) with Not_found -> None

let find_name_in dp name =
  match Coq.Module.make dp with
  | Error err -> Error (err_code, lp_to_string err)
  | Ok mod_ -> (
    let uri = Coq.Module.uri mod_ in
    match Coq.Module.find mod_ name with
    | Error err -> Error (err_code, err)
    | Ok range -> Ok (Option.map (fun range -> Location.{ uri; range }) range))

let get_from_file id_at_point =
  Fleche.Io.Log.trace "rq_definition" "get_from_file";
  let qid = Libnames.qualid_of_string id_at_point in
  match locate_extended qid with
  | Some (TrueGlobal (ConstRef cr)) ->
    Fleche.Io.Log.trace "rq_definition" "TrueGlobal Found";
    let dp = Names.Constant.modpath cr |> Names.ModPath.dp in
    let name = Names.Constant.to_string cr in
    find_name_in dp name
  | Some (TrueGlobal (IndRef (ind, _idx))) ->
    let dp = Names.MutInd.modpath ind |> Names.ModPath.dp in
    let name = Names.MutInd.to_string ind in
    find_name_in dp name
  | Some (Abbrev _abbrev) ->
    (* Needs improved .glob parsing *)
    Ok None
  | _ ->
    Fleche.Io.Log.trace "rq_definition" "No TrueGlobal Found";
    Ok None

let get_from_import require_at_point =
  match Loadpath.locate_qualified_library require_at_point with
  | Ok (dp, _file) -> (
    match Coq.Module.make dp with
    | Error _err -> None
    | Ok mod_ ->
      let uri = Coq.Module.uri mod_ in
      let start = Lang.Point.{ line = 0; character = 0; offset = 0 } in
      let range = Lang.Range.{ start; end_ = start } in
      Some Location.{ uri; range })
  | Error _ -> None

let get_from_file_or_import ~token ~st id_at_point =
  let f id =
    match get_from_file id with
    | Error err -> Error err
    | Ok (Some res) -> Ok (Some res)
    | Ok None ->
      let qualid = Libnames.qualid_of_string id_at_point in
      Ok (get_from_import qualid)
  in
  Coq.State.in_state ~token ~st ~f id_at_point

let request ~token ~(doc : Fleche.Doc.t) ~point =
  let { Fleche.Doc.contents; _ } = doc in
  let ok s = Coq.Protect.E.ok (Result.Ok s) in
  let idp = Rq_common.get_id_at_point ~contents ~point in
  Option.cata
    (fun idp ->
      match get_from_toc ~doc idp with
      | Some loc -> ok (Some loc)
      | None ->
        let approx = Fleche.Info.PrevIfEmpty in
        Fleche.Info.LC.node ~doc ~point approx
        |> Option.cata
             (fun node ->
               let st = Fleche.Doc.Node.state node in
               get_from_file_or_import ~token ~st idp)
             (ok None))
    (ok None) idp
  |> Coq.Protect.E.map ~f:(Result.map (Option.cata Location.to_yojson `Null))

let request ~token ~doc ~point =
  let name = "textDocument/definition" in
  let f () = request ~token ~doc ~point in
  Request.R.of_execution ~name ~f ()
