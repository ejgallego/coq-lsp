(* Flèche Coq compiler *)
open Cmdliner
open Fcc_lib

let fcc_main int_backend roots display debug plugins files coqlib coqcorelib
    ocamlpath rload_path load_path require_libraries no_vo max_errors =
  let vo_load_path = rload_path @ load_path in
  let ml_include_path = [] in
  let args = [] in
  let cmdline =
    { Coq.Workspace.CmdLine.coqlib
    ; coqcorelib
    ; ocamlpath
    ; vo_load_path
    ; ml_include_path
    ; args
    ; require_libraries
    }
  in
  let plugins = Args.compute_default_plugins ~no_vo ~plugins in
  let args =
    Args.{ cmdline; roots; display; files; debug; plugins; max_errors }
  in
  Driver.go ~int_backend args

(****************************************************************************)
(* Specific to fcc *)
let display : Args.Display.t Term.t =
  let doc = "Verbosity display settings" in
  let dparse =
    Args.Display.[ ("verbose", Verbose); ("normal", Normal); ("quiet", Quiet) ]
  in
  Arg.(
    value
    & opt (enum dparse) Args.Display.Normal
    & info [ "display" ] ~docv:"DISPLAY" ~doc)

let file : string list Term.t =
  let doc = "File(s) to compile" in
  Arg.(value & pos_all string [] & info [] ~docv:"FILES" ~doc)

let plugins : string list Term.t =
  let doc = "Compiler plugins to load" in
  Arg.(value & opt_all string [] & info [ "plugin" ] ~docv:"PLUGINS" ~doc)

let no_vo : bool Term.t =
  let doc = "Don't generate .vo files at the end of compilation" in
  Arg.(value & flag & info [ "no_vo" ] ~doc)

let max_errors : int option Term.t =
  let doc = "Maximum errors in files before aborting" in
  Arg.(
    value & opt (some int) None & info [ "max_errors" ] ~docv:"MAX_ERRORS" ~doc)

module Exit_codes = struct
  let fatal : Cmd.Exit.info =
    let doc =
      "A fatal error was found. This is typically due to `--max_errors` being \
       triggered, but also failures in library / Coq setup will trigger this."
    in
    Cmd.Exit.info ~doc 1

  let stopped : Cmd.Exit.info =
    let doc =
      "The document was not fully checked: this is often due to a timeout, \
       interrupt, or resource limit."
    in
    Cmd.Exit.info ~doc 2

  let scheduled : Cmd.Exit.info =
    let doc = "[INTERNAL] File not scheduled" in
    Cmd.Exit.info ~doc 102

  let uri_failed : Cmd.Exit.info =
    let doc = "[INTERNAL] URI failed" in
    Cmd.Exit.info ~doc 222
end

let fcc_cmd : int Cmd.t =
  let doc = "Flèche Coq Compiler" in
  let man =
    [ `S "DESCRIPTION"
    ; `P "Flèche Coq Compiler"
    ; `S "USAGE"
    ; `P "See the documentation on the project's webpage for more information"
    ]
  in
  let version = Fleche.Version.server in
  let fcc_term =
    let open Coq.Args in
    Term.(
      const fcc_main $ int_backend $ roots $ display $ debug $ plugins $ file
      $ coqlib $ coqcorelib $ ocamlpath $ rload_paths $ qload_paths $ ri_from
      $ no_vo $ max_errors)
  in
  let exits = Exit_codes.[ fatal; stopped; scheduled; uri_failed ] in
  Cmd.(v (Cmd.info "fcc" ~exits ~version ~doc ~man) fcc_term)

let main () =
  let ecode = Cmd.eval' fcc_cmd in
  exit ecode

let () = main ()
