let init_coq ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { debug; load_module; load_plugin })

let cmdline : Coq.Workspace.CmdLine.t =
  { coqlib = Coq_config.coqlib
  ; coqcorelib = Filename.concat Coq_config.coqlib "../coq-core"
  ; ocamlpath = None
  ; vo_load_path = []
  ; ml_include_path = []
  ; args = []
  ; require_libraries = []
  }

let setup_workspace ~token ~init ~debug ~root =
  let dir = Lang.LUri.File.to_string_file root in
  (let open Coq.Compat.Result.O in
   let+ workspace = Coq.Workspace.guess ~token ~debug ~cmdline ~dir in
   let files = Coq.Files.make () in
   Fleche.Doc.Env.make ~init ~workspace ~files)
  |> Result.map_error (fun msg -> Agent.Error.Coq msg)

let trace_stderr hdr ?extra:_ msg =
  Format.eprintf "@[[trace] %s | %s @]@\n%!" hdr msg

let trace_ref = ref trace_stderr

let message_stderr ~lvl:_ ~message =
  Format.eprintf "@[[message] %s @]@\n%!" message

let message_ref = ref message_stderr

let io =
  let trace hdr ?extra msg = !trace_ref hdr ?extra msg in
  let message ~lvl ~message = !message_ref ~lvl ~message in
  let diagnostics ~uri:_ ~version:_ _diags = () in
  let fileProgress ~uri:_ ~version:_ _pinfo = () in
  let perfData ~uri:_ ~version:_ _perf = () in
  let serverVersion _ = () in
  let serverStatus _ = () in
  { Fleche.Io.CallBack.trace
  ; message
  ; diagnostics
  ; fileProgress
  ; perfData
  ; serverVersion
  ; serverStatus
  }

let init_st = ref None

(* To be moved to pet *)
let init_agent ~debug =
  init_st := Some (init_coq ~debug);
  Fleche.Io.CallBack.set io

let env = ref None

let set_workspace ~token ~debug ~root =
  let init = Option.get !init_st in
  let open Coq.Compat.Result.O in
  let+ env_ = setup_workspace ~token ~init ~debug ~root in
  env := Some env_

(* likely duplicated somewhere else *)
let pp_diag fmt { Lang.Diagnostic.message; _ } =
  Format.fprintf fmt "%a" Pp.pp_with message

let print_diags (doc : Fleche.Doc.t) =
  let d = Fleche.Doc.diags doc in
  Format.(eprintf "@[<v>%a@]" (pp_print_list pp_diag) d)

let read_raw ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  try Ok Coq.Compat.Ocaml_414.In_channel.(with_open_text file input_all)
  with Sys_error err -> Error (Agent.Error.Coq err)

let setup_doc ~token env uri =
  match read_raw ~uri with
  | Ok raw ->
    let doc = Fleche.Doc.create ~token ~env ~uri ~version:0 ~raw in
    print_diags doc;
    let target = Fleche.Doc.Target.End in
    Ok (Fleche.Doc.check ~io ~token ~target ~doc ())
  | Error err -> Error err

let fn ~token uri =
  let env = Option.get !env in
  setup_doc ~token env uri
