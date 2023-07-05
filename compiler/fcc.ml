(* Flèche Coq compiler *)
open Cmdliner
open Fcc_lib

let fcc_main roots display debug plugins files =
  let args = Args.{ roots; display; files; debug; plugins } in
  Driver.go args

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

let debug : bool Term.t =
  let doc = "Enable debug mode" in
  Arg.(value & flag & info [ "debug" ] ~docv:"DISPLAY" ~doc)

let file : string list Term.t =
  let doc = "File(s) to compile" in
  Arg.(value & pos_all string [] & info [] ~docv:"FILES" ~doc)

let plugins : string list Term.t =
  let doc = "Compiler plugins to load" in
  Arg.(value & opt_all string [] & info [ "plugin" ] ~docv:"PLUGINS" ~doc)

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
    Term.(const fcc_main $ roots $ display $ debug $ plugins $ file)
  in
  Cmd.(v (Cmd.info "fcc" ~version ~doc ~man) fcc_term)

let main () =
  let ecode = Cmd.eval fcc_cmd in
  exit ecode

let () = main ()
