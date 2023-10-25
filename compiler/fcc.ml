(* Flèche Coq compiler *)
open Cmdliner
open Fcc_lib

let fcc_main roots display debug plugins files coqlib coqcorelib ocamlpath
    rload_path load_path require_libraries =
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
  let args = Args.{ cmdline; roots; display; files; debug; plugins } in
  Driver.go args

(****************************************************************************)
(* XXX: Common with coq-lsp.exe *)
let coqlib =
  let doc =
    "Load Coq.Init.Prelude from $(docv); theories and user-contrib should live \
     there."
  in
  Arg.(
    value & opt string Coq_config.coqlib & info [ "coqlib" ] ~docv:"COQLIB" ~doc)

let coqcorelib =
  let doc = "Path to Coq plugin directories." in
  Arg.(
    value
    & opt string (Filename.concat Coq_config.coqlib "../coq-core/")
    & info [ "coqcorelib" ] ~docv:"COQCORELIB" ~doc)

let ocamlpath =
  let doc = "Path to OCaml's lib" in
  Arg.(
    value & opt (some string) None & info [ "ocamlpath" ] ~docv:"OCAMLPATH" ~doc)

let coq_lp_conv ~implicit (unix_path, lp) =
  { Loadpath.coq_path = Libnames.dirpath_of_string lp
  ; unix_path
  ; has_ml = true
  ; implicit
  ; recursive = true
  }

let rload_path : Loadpath.vo_path list Term.t =
  let doc =
    "Bind a logical loadpath LP to a directory DIR and implicitly open its \
     namespace."
  in
  Term.(
    const List.(map (coq_lp_conv ~implicit:true))
    $ Arg.(
        value
        & opt_all (pair dir string) []
        & info [ "R"; "rec-load-path" ] ~docv:"DIR,LP" ~doc))

let load_path : Loadpath.vo_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Term.(
    const List.(map (coq_lp_conv ~implicit:false))
    $ Arg.(
        value
        & opt_all (pair dir string) []
        & info [ "Q"; "load-path" ] ~docv:"DIR,LP" ~doc))
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

let debug : bool Term.t =
  let doc = "Enable debug mode" in
  Arg.(value & flag & info [ "debug" ] ~docv:"DISPLAY" ~doc)

let file : string list Term.t =
  let doc = "File(s) to compile" in
  Arg.(value & pos_all string [] & info [] ~docv:"FILES" ~doc)

let plugins : string list Term.t =
  let doc = "Compiler plugins to load" in
  Arg.(value & opt_all string [] & info [ "plugin" ] ~docv:"PLUGINS" ~doc)

let rifrom : (string option * string) list Term.t =
  let doc =
    "FROM Require Import LIBRARY before creating the document, à la From Coq \
     Require Import Prelude"
  in
  Term.(
    const (List.map (fun (x, y) -> (Some x, y)))
    $ Arg.(
        value
        & opt_all (pair string string) []
        & info [ "rifrom"; "require-import-from" ] ~docv:"FROM,LIBRARY" ~doc))

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
    Term.(
      const fcc_main $ roots $ display $ debug $ plugins $ file $ coqlib
      $ coqcorelib $ ocamlpath $ rload_path $ load_path $ rifrom)
  in
  Cmd.(v (Cmd.info "fcc" ~version ~doc ~man) fcc_term)

let main () =
  let ecode = Cmd.eval fcc_cmd in
  exit ecode

let () = main ()
