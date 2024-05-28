(************************************************************************)
(* Flèche => document manager: Document                                 *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

open Cmdliner

(****************************************************************************)
(* Common Coq command-line arguments *)
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

let rload_paths : Loadpath.vo_path list Term.t =
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

let qload_paths : Loadpath.vo_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Term.(
    const List.(map (coq_lp_conv ~implicit:false))
    $ Arg.(
        value
        & opt_all (pair dir string) []
        & info [ "Q"; "load-path" ] ~docv:"DIR,LP" ~doc))

let debug : bool Term.t =
  let doc = "Enable debug mode" in
  Arg.(value & flag & info [ "debug" ] ~doc)

let bt =
  let doc = "Enable backtraces" in
  Cmdliner.Arg.(value & flag & info [ "bt" ] ~doc)

let ml_include_path : string list Term.t =
  let doc = "Include DIR in default loadpath, for locating ML files" in
  Arg.(
    value & opt_all dir [] & info [ "I"; "ml-include-path" ] ~docv:"DIR" ~doc)

let ri_from : (string option * string) list Term.t =
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

let int_backend =
  let doc =
    "Select Interruption Backend, if absent, the best available for your OCaml \
     version will be selected"
  in
  Arg.(
    value
    & opt (enum [ ("Coq", Some Limits.Coq); ("Mp", Some Limits.Mp) ]) None
    & info [ "int_backend" ] ~docv:"INT_BACKEND" ~doc)

let roots : string list Term.t =
  let doc = "Workspace(s) root(s)" in
  Arg.(value & opt_all string [] & info [ "root" ] ~docv:"ROOTS" ~doc)

let coq_diags_level : int Term.t =
  let doc =
    "Controsl whether Coq Info and Notice message appear in diagnostics.\n\
    \ 0 = None; 1 = Notices, 2 = Notices and Info"
  in
  Arg.(value & opt int 0 & info [ "diags_level" ] ~docv:"DIAGS_LEVEL" ~doc)
