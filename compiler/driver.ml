(* Duplicated with coq_lsp *)
let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { debug; load_module; load_plugin })

let replace_test_path exp message =
  let home_re = Str.regexp (exp ^ ".*$") in
  Str.global_replace home_re (exp ^ "[TEST_PATH]") message

let fcc_test = Sys.getenv_opt "FCC_TEST"

let sanitize_paths message =
  match fcc_test with
  | None -> message
  | Some _ ->
    message
    |> replace_test_path "coqlib is at: "
    |> replace_test_path "coqcorelib is at: "
    |> replace_test_path "findlib config: "
    |> replace_test_path "findlib default location: "

let log_workspace ~io (dir, w) =
  let message, extra = Coq.Workspace.describe_guess w in
  Fleche.Io.Log.trace "workspace" ~extra "initialized %s" dir;
  let lvl = Fleche.Io.Level.Info in
  let message = sanitize_paths message in
  Fleche.Io.Report.message ~io ~lvl ~message

let load_plugin plugin_name = Fl_dynload.load_packages [ plugin_name ]
let plugin_init = List.iter load_plugin

let apply_config ~max_errors =
  Option.iter
    (fun max_errors -> Fleche.Config.v := { !Fleche.Config.v with max_errors })
    max_errors

let go ~int_backend args =
  let { Args.cmdline
      ; roots
      ; display
      ; debug
      ; files
      ; plugins
      ; max_errors
      ; coq_diags_level
      } =
    args
  in
  (* Initialize event callbacks, in testing don't do perfData *)
  let perfData = Option.is_empty fcc_test in
  let io = Output.init ~display ~perfData ~coq_diags_level in
  (* Initialize Coq *)
  let debug = debug || Fleche.Debug.backtraces || !Fleche.Config.v.debug in
  let root_state = coq_init ~debug in
  let roots = if List.length roots < 1 then [ Sys.getcwd () ] else roots in
  let default = Coq.Workspace.default ~debug ~cmdline in
  let () = Coq.Limits.select_best int_backend in
  let () = Coq.Limits.start () in
  let token = Coq.Limits.Token.create () in
  let workspaces =
    List.map
      (fun dir -> (dir, Coq.Workspace.guess ~token ~cmdline ~debug ~dir))
      roots
  in
  List.iter (log_workspace ~io) workspaces;
  let () = apply_config ~max_errors in
  let cc = Cc.{ root_state; workspaces; default; io; token } in
  (* Initialize plugins *)
  plugin_init plugins;
  Compile.compile ~cc files
