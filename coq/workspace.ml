(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Setup = struct
  type t =
    { vo_load_path : Loadpath.vo_path list
    ; ml_include_path : string list
    ; options : (Goptions.option_name * Coqargs.option_command) list
          (** This includes warnings *)
    }

  let append base { vo_load_path; ml_include_path; options } =
    { vo_load_path = base.vo_load_path @ vo_load_path
    ; ml_include_path = base.ml_include_path @ ml_include_path
    ; options = base.options @ options
    }
end

type t = Setup.t * string
(* | CoqProject of Setup.t *)
(* | Dune *)

let apply ({ Setup.vo_load_path; ml_include_path; options }, _) =
  List.iter Mltop.add_ml_dir ml_include_path;
  List.iter Loadpath.add_vo_path vo_load_path;
  List.iter Coqargs.set_option options;
  ()

(* TODO, parse _CoqProject extra_args in Coq format *)
let parse_coq_args _ = []

let loadpath_from_coqproject () : Setup.t =
  (* Io.Log.error "init" "Parsing _CoqProject"; *)
  let open CoqProject_file in
  let to_vo_loadpath f implicit =
    let open Loadpath in
    let unix_path, coq_path = f in
    (* Lsp.Io.log_error "init"
     *   (Printf.sprintf "Path from _CoqProject: %s %s" unix_path.path coq_path); *)
    { implicit
    ; recursive = true
    ; has_ml = false
    ; unix_path = unix_path.path
    ; coq_path = Libnames.dirpath_of_string coq_path
    }
  in
  let { r_includes; q_includes; ml_includes; extra_args; _ } =
    read_project_file ~warning_fn:(fun _ -> ()) "_CoqProject"
  in
  let ml_include_path = List.map (fun f -> f.thing.path) ml_includes in
  let vo_path = List.map (fun f -> to_vo_loadpath f.thing false) q_includes in
  let vo_load_path =
    List.append vo_path
      (List.map (fun f -> to_vo_loadpath f.thing true) r_includes)
  in
  let options = parse_coq_args extra_args in
  { vo_load_path; ml_include_path; options }

let coq_loadpath_default ~implicit coq_path =
  let mk_path prefix = coq_path ^ "/" ^ prefix in
  let mk_lp ~ml ~root ~dir ~implicit =
    { Loadpath.unix_path = mk_path dir
    ; coq_path = root
    ; has_ml = ml
    ; implicit
    ; recursive = true
    }
  in
  let coq_root = Names.DirPath.make [ Libnames.coq_root ] in
  let default_root = Libnames.default_root_prefix in
  { Setup.vo_load_path =
      [ mk_lp ~ml:false ~root:coq_root ~implicit ~dir:"theories"
      ; mk_lp ~ml:true ~root:default_root ~implicit:false ~dir:"user-contrib"
      ]
  ; ml_include_path =
      (let unix_path = Filename.concat coq_path "../coq-core/plugins" in
       System.all_subdirs ~unix_path |> List.map fst)
  ; options = []
  }

(* We append the default loadpath, TODO, support -noinit *)
let guess ~coqlib ~cmdline =
  let vo_workspace, origin =
    if Sys.file_exists "_CoqProject" then
      ( loadpath_from_coqproject ()
      , Filename.concat (Sys.getcwd ()) "_CoqProject" )
    else (cmdline, "Command-line arguments")
  in
  ( Setup.append (coq_loadpath_default ~implicit:false coqlib) vo_workspace
  , origin )
