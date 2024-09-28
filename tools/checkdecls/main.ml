(* Flèche Coq compiler / checkdecls for Coq-blueprints *)

let cd_main roots debug files coqlib coqcorelib findlib_config ocamlpath
    rload_path load_path require_libraries =
  let vo_load_path = rload_path @ load_path in
  let ml_include_path = [] in
  let args = [] in
  let cmdline =
    { Coq.Workspace.CmdLine.coqlib
    ; coqcorelib
    ; findlib_config
    ; ocamlpath
    ; vo_load_path
    ; ml_include_path
    ; args
    ; require_libraries
    }
  in
  Driver.go ~cmdline ~roots ~debug ~files

open Cmdliner

(****************************************************************************)
let files : string list Term.t =
  let doc = "Files with list of identifiers to check" in
  Arg.(non_empty & pos_all non_dir_file [] & info [] ~docv:"FILES" ~doc)

module Exit_codes = struct
  let missing_id : Cmd.Exit.info =
    let doc = "An input identifier was not found" in
    Cmd.Exit.info ~doc 1

  let stopped : Cmd.Exit.info =
    let doc =
      "The document was not fully checked: this is often due to a timeout, \
       interrupt, or resource limit."
    in
    Cmd.Exit.info ~doc 2

  let uri_failed : Cmd.Exit.info =
    let doc =
      "[INTERNAL] There was an internal error setting up the Coq workspace"
    in
    Cmd.Exit.info ~doc 222
end

let cd_cmd : int Cmd.t =
  let doc = "CheckDecls for Coq" in
  let man =
    [ `S "DESCRIPTION"
    ; `P "checkdecls checker"
    ; `S "USAGE"
    ; `P "See the documentation of blueprints"
    ]
  in
  (* let version = Fleche.Version.server in *)
  let version = "0.1" in
  let fcc_term =
    let open Coq.Args in
    Term.(
      const cd_main $ roots $ debug $ files $ coqlib $ coqcorelib
      $ findlib_config $ ocamlpath $ rload_paths $ qload_paths $ ri_from)
  in
  let exits = Exit_codes.[ missing_id; stopped; uri_failed ] in
  Cmd.(v (Cmd.info "checkdecls" ~exits ~version ~doc ~man) fcc_term)

let main () =
  let ecode = Cmd.eval' cd_cmd in
  exit ecode

let () = main ()
