open Fleche

let is_in_dir ~dir ~file = CString.is_prefix dir file

let workspace_of_uri ~io ~uri ~workspaces =
  let file = Lang.LUri.File.to_string_file uri in
  match List.find_opt (fun (dir, _) -> is_in_dir ~dir ~file) workspaces with
  | None ->
    Io.Report.message ~io ~lvl:1 ~message:("file not in workspace: " ^ file);
    snd (List.hd workspaces)
  | Some (_, workspace) -> workspace

(* Improve errors *)
let save_vo_file ~doc =
  match Fleche.Doc.save ~doc with
  | { r = Completed (Ok ()); feedback = _ } -> ()
  | { r = Completed (Error _); feedback = _ } -> ()
  | { r = Interrupted; feedback = _ } -> ()

let save_diags_file ~(doc : Fleche.Doc.t) =
  let file = Lang.LUri.File.to_string_file doc.uri in
  let file = Filename.remove_extension file ^ ".diags" in
  let diags = Fleche.Doc.diags doc in
  Util.format_to_file ~file ~f:Output.pp_diags diags

let compile_file ~cc file =
  let { Cc.io; root_state; workspaces } = cc in
  io.message ~lvl:3 ~message:(Format.asprintf "compiling file %s@\n%!" file);
  match Lang.LUri.(File.of_uri (of_string file)) with
  | Error _ -> ()
  | Ok uri -> (
    let workspace = workspace_of_uri ~io ~workspaces ~uri in
    let env = Doc.Env.make ~init:root_state ~workspace in
    let raw = Util.input_all file in
    let () = Theory.create ~io ~env ~uri ~raw ~version:1 in
    match Theory.Check.maybe_check ~io with
    | None -> ()
    | Some (_, doc) ->
      save_vo_file ~doc;
      save_diags_file ~doc;
      Theory.close ~uri)

let compile ~cc = List.iter (compile_file ~cc)
