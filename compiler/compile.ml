open Fleche

let is_in_dir ~dir ~file = CString.is_prefix dir file

let workspace_of_uri ~io ~uri ~workspaces ~default =
  let file = Lang.LUri.File.to_string_file uri in
  match List.find_opt (fun (dir, _) -> is_in_dir ~dir ~file) workspaces with
  | None ->
    let lvl = Io.Level.error in
    let message = "file not in workspace: " ^ file in
    Io.Report.message ~io ~lvl ~message;
    default
  | Some (_, Error err) ->
    let lvl = Io.Level.error in
    let message = "invalid workspace for: " ^ file ^ " " ^ err in
    Io.Report.message ~io ~lvl ~message;
    default
  | Some (_, Ok workspace) -> workspace

(** Move to a plugin *)
let save_diags_file ~(doc : Fleche.Doc.t) =
  let file = Lang.LUri.File.to_string_file doc.uri in
  let file = Filename.remove_extension file ^ ".diags" in
  let diags = Fleche.Doc.diags doc in
  Util.format_to_file ~file ~f:Output.pp_diags diags

let compile_file ~cc file =
  let { Cc.io; root_state; workspaces; default; token } = cc in
  let lvl = Io.Level.info in
  let message = Format.asprintf "compiling file %s@\n%!" file in
  io.message ~lvl ~message;
  match Lang.LUri.(File.of_uri (of_string file)) with
  | Error _ -> ()
  | Ok uri -> (
    let workspace = workspace_of_uri ~io ~workspaces ~uri ~default in
    let files = Coq.Files.make () in
    let env = Doc.Env.make ~init:root_state ~workspace ~files in
    let raw = Util.input_all file in
    let () = Theory.create ~io ~token ~env ~uri ~raw ~version:1 in
    match Theory.Check.maybe_check ~io ~token with
    | None -> ()
    | Some (_, doc) ->
      save_diags_file ~doc;
      (* Vo file saving is now done by a plugin *)
      Theory.close ~uri)

let compile ~cc = List.iter (compile_file ~cc)
