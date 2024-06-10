open Fleche

let is_in_dir ~dir ~file = CString.is_prefix dir file

let workspace_of_uri ~io ~uri ~workspaces ~default =
  let file = Lang.LUri.File.to_string_file uri in
  match List.find_opt (fun (dir, _) -> is_in_dir ~dir ~file) workspaces with
  | None ->
    Io.Report.msg ~io ~lvl:Error "file not in workspace: %s" file;
    default
  | Some (_, Error err) ->
    Io.Report.msg ~io ~lvl:Error "invalid workspace for: %s %s" file err;
    default
  | Some (_, Ok workspace) -> workspace

(** Move to a plugin *)
let save_diags_file ~(doc : Fleche.Doc.t) =
  let file = Lang.LUri.File.to_string_file doc.uri in
  let file = Filename.remove_extension file ^ ".diags" in
  let diags = Fleche.Doc.diags doc in
  Coq.Compat.format_to_file ~file ~f:Output.pp_diags diags

(** Return: exit status for file:

    - 1: fatal error in checking (usually due to [max_errors=n]
    - 2: checking stopped
    - 102: file not scheduled
    - 222: Incorrect URI *)
let status_of_doc (doc : Doc.t) =
  match doc.completed with
  | Yes _ -> 0
  | Stopped _ -> 2
  | Failed _ -> 1

let compile_file ~cc file : int =
  let { Cc.io; root_state; workspaces; default; token } = cc in
  Io.Report.msg ~io ~lvl:Info "compiling file %s" file;
  match Lang.LUri.(File.of_uri (of_string file)) with
  | Error _ -> 222
  | Ok uri -> (
    let workspace = workspace_of_uri ~io ~workspaces ~uri ~default in
    let files = Coq.Files.make () in
    let env = Doc.Env.make ~init:root_state ~workspace ~files in
    let raw = Coq.Compat.Ocaml_414.In_channel.(with_open_bin file input_all) in
    let () = Theory.create ~io ~token ~env ~uri ~raw ~version:1 in
    match Theory.Check.maybe_check ~io ~token with
    | None -> 102
    | Some (_, doc) ->
      save_diags_file ~doc;
      (* Vo file saving is now done by a plugin *)
      Theory.close ~uri;
      status_of_doc doc)

let compile ~cc =
  List.fold_left
    (fun status file -> if status = 0 then compile_file ~cc file else status)
    0
