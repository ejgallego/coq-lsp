(* Duplicated with coq_lsp *)
let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { debug; load_module; load_plugin })

let replace_test_path exp message =
  let home_re = Str.regexp (exp ^ ".*$") in
  Str.global_replace home_re (exp ^ "[TEST_PATH]") message

let sanitize_paths message =
  match Sys.getenv_opt "FCC_TEST" with
  | None -> message
  | Some _ ->
    message
    |> replace_test_path "coqlib is at: "
    |> replace_test_path "coqcorelib is at: "
    |> replace_test_path "findlib config: "
    |> replace_test_path "findlib default location: "

let log_workspace ~io (dir, w) =
  let message, extra = Coq.Workspace.describe w in
  Fleche.Io.Log.trace "workspace" ("initialized " ^ dir) ~extra;
  let lvl = Fleche.Io.Level.info in
  let message = sanitize_paths message in
  Fleche.Io.Report.message ~io ~lvl ~message

let load_plugin plugin_name = Fl_dynload.load_packages [ plugin_name ]
let plugin_init = List.iter load_plugin

let go args =
  let { Args.cmdline; roots; display; debug; files; plugins } = args in
  (* Initialize event callbacks *)
  let io = Output.init display in
  (* Initialize Coq *)
  let debug = debug || Fleche.Debug.backtraces || !Fleche.Config.v.debug in
  let root_state = coq_init ~debug in
  let roots = if List.length roots < 1 then [ Sys.getcwd () ] else roots in
  let workspaces =
    List.map (fun dir -> (dir, Coq.Workspace.guess ~cmdline ~debug ~dir)) roots
  in
  List.iter (log_workspace ~io) workspaces;
  let cc = Cc.{ root_state; workspaces; io } in
  (* Initialize plugins *)
  plugin_init plugins;
  Compile.compile ~cc files
