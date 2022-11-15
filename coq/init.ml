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

type opts =
  { msg_handler : Message.t -> unit  (** callback to handle async feedback *)
  ; load_module : string -> unit  (** callback to load cma/cmo files *)
  ; load_plugin : Mltop.PluginSpec.t -> unit
        (** callback to load findlib packages *)
  ; debug : bool  (** Enable Coq Debug mode *)
  }

let init opts =
  (* Core Coq initialization *)
  Lib.init ();
  Global.set_impredicative_set false;
  Flags.set_native_compiler false;
  Global.set_native_compiler false;

  if opts.debug then CDebug.set_flags "backtrace";

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  let lvl_to_severity (lvl : Feedback.level) =
    match lvl with
    | Feedback.Debug -> 5
    | Feedback.Info -> 4
    | Feedback.Notice -> 3
    | Feedback.Warning -> 2
    | Feedback.Error -> 1
  in

  let fb_handler = function
    | Feedback.{ contents = Message (lvl, loc, msg); _ } ->
      let lvl = lvl_to_severity lvl in
      opts.msg_handler (loc, lvl, msg)
    | _ -> ()
  in
  ignore (Feedback.add_feeder fb_handler);

  (* SerAPI plugins *)
  let load_plugin = opts.load_plugin in
  let load_module = opts.load_module in

  (* Custom toplevel is used for bytecode-to-js dynlink *)
  let ser_mltop : Mltop.toplevel =
    let open Mltop in
    { load_plugin
    ; load_module
    ; add_dir = (fun _ -> ())
    ; ml_loop = (fun _ -> ())
    }
  in
  Mltop.set_top ser_mltop;

  (**************************************************************************)
  (* Add root state!!                                                       *)
  (**************************************************************************)
  Vernacstate.freeze_interp_state ~marshallable:false |> State.Internal.of_coq

(* End of initialization *)

let loadpath_from_coqproject () : Loadpath.vo_path list =
  if not (Sys.file_exists "_CoqProject") then []
  else
    let (* Io.Log.error "init" "Parsing _CoqProject"; *)
    open CoqProject_file in
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
    let { r_includes; q_includes; _ } =
      read_project_file ~warning_fn:(fun _ -> ()) "_CoqProject"
    in
    let vo_path = List.map (fun f -> to_vo_loadpath f.thing false) q_includes in
    List.append vo_path
      (List.map (fun f -> to_vo_loadpath f.thing true) r_includes)

(* Inits the context for a document *)
module Doc = struct
  type require_decl =
    string * string option * Vernacexpr.export_with_cats option

  type env =
    { vo_load_path : Loadpath.vo_path list
    ; ml_load_path : string list
    ; requires : require_decl list
    }

  let make ~root_state ~env ~name =
    (* Lsp.Io.log_error "init" "starting"; *)
    Vernacstate.unfreeze_interp_state (State.Internal.to_coq root_state);

    (* This should go away in Coq itself *)
    Safe_typing.allow_delayed_constants := true;
    let load_objs libs =
      let rq_file (dir, from, exp) =
        let mp = Libnames.qualid_of_string dir in
        let mfrom = Option.map Libnames.qualid_of_string from in
        Flags.silently
          (Vernacentries.vernac_require mfrom exp)
          [ (mp, Vernacexpr.ImportAll) ]
      in
      List.(iter rq_file (rev libs))
    in

    (* Set load path; important, this has to happen before we declare the
       library below as [Declaremods/Library] will infer the module name by
       looking at the load path! *)
    List.iter Mltop.add_ml_dir env.ml_load_path;
    List.iter Loadpath.add_vo_path env.vo_load_path;
    List.iter Loadpath.add_vo_path (loadpath_from_coqproject ());
    Declaremods.start_library name;

    (* Import initial libraries. *)
    load_objs env.requires;

    (* We return the state at this point! *)
    Vernacstate.freeze_interp_state ~marshallable:false |> State.Internal.of_coq
end
