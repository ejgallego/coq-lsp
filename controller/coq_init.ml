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
(* Coq Language Server Protocol / SerAPI                                *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)

type coq_opts =
  { fb_handler : Feedback.feedback -> unit
        (** callback to handle async feedback *)
  ; ml_load : (string -> unit) option  (** callback to load cma/cmo files *)
  ; debug : bool  (** Enable Coq Debug mode *)
  }

let coq_init opts =
  if opts.debug then (
    Printexc.record_backtrace true;
    CDebug.set_flags "misc");

  (* Core Coq initialization *)
  Lib.init ();
  Global.set_impredicative_set false;
  Flags.set_native_compiler false;
  Global.set_native_compiler false;

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  ignore (Feedback.add_feeder opts.fb_handler);

  (**************************************************************************)
  (* Add root state!!                                                       *)
  (**************************************************************************)
  Vernacstate.freeze_interp_state ~marshallable:false
(* End of initialization *)

let loadpath_from_coqproject () : Loadpath.vo_path list =
  if not (Sys.file_exists "_CoqProject") then []
  else (
    Lsp.Io.log_error "init" "Parsing _CoqProject";
    let open CoqProject_file in
    let to_vo_loadpath f implicit =
      let open Loadpath in
      let unix_path, coq_path = f in
      Lsp.Io.log_error "init"
        (Printf.sprintf "Path from _CoqProject: %s %s" unix_path.path coq_path);
      { implicit
      ; recursive = true
      ; has_ml = false
      ; unix_path = unix_path.path
      ; coq_path = Libnames.dirpath_of_string coq_path
      }
    in
    let { r_includes; q_includes; _ } =
      read_project_file ~warning_fn:(fun _ -> ()) "_CoqProject"
    in
    let vo_path = List.map (fun f -> to_vo_loadpath f.thing false) q_includes in
    List.append vo_path
      (List.map (fun f -> to_vo_loadpath f.thing true) r_includes))

(* Inits the context for a document *)
let doc_init ~root_state ~vo_load_path ~ml_include_path ~libname ~require_libs =
  Vernacstate.unfreeze_interp_state root_state;

  (* This should go away in Coq itself *)
  Safe_typing.allow_delayed_constants := true;
  let load_objs libs =
    let rq_file (dir, from, exp) =
      let mp = Libnames.qualid_of_string dir in
      let mfrom = Option.map Libnames.qualid_of_string from in
      Flags.silently (Vernacentries.vernac_require mfrom exp) [ mp ]
    in
    List.(iter rq_file (rev libs))
  in

  (* Set load path; important, this has to happen before we declare the library
     below as [Declaremods/Library] will infer the module name by looking at the
     load path! *)
  List.iter Mltop.add_ml_dir ml_include_path;
  List.iter Loadpath.add_vo_path vo_load_path;
  List.iter Loadpath.add_vo_path (loadpath_from_coqproject ());
  Declaremods.start_library libname;

  (* Import initial libraries. *)
  load_objs require_libs;

  (* We return the state at this point! *)
  Vernacstate.freeze_interp_state ~marshallable:false
