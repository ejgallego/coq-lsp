(* Flèche Coq compiler *)
open Cmdliner
open Fcc_lib

let fcc_main roots display debug plugins files coqlib coqcorelib ocamlpath
    rload_path load_path require_libraries no_vo =
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
  let args = Args.{ cmdline; roots; display; files; debug; plugins } in
  Driver.go args

(****************************************************************************)

(* Specific to fcc *)
let roots : string list Term.t =
  let doc = "Workspace(s) root(s)" in
  Arg.(value & opt_all string [] & info [ "root" ] ~docv:"ROOTS" ~doc)

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

let fcc_cmd : unit Cmd.t =
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
      const fcc_main $ roots $ display $ debug $ plugins $ file $ coqlib
      $ coqcorelib $ ocamlpath $ rload_paths $ qload_paths $ ri_from $ no_vo)
  in
  Cmd.(v (Cmd.info "fcc" ~version ~doc ~man) fcc_term)

let main () =
  let ecode = Cmd.eval fcc_cmd in
  exit ecode

let () = main ()
