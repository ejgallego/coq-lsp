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
  { load_module : string -> unit  (** callback to load cma/cmo files *)
  ; load_plugin : Mltop.PluginSpec.t -> unit
        (** callback to load findlib packages *)
  ; debug : bool  (** Enable Coq Debug mode *)
  }

let coq_lvl_to_severity (lvl : Feedback.level) =
  let open Lang.Diagnostic.Severity in
  match lvl with
  | Feedback.Debug -> hint (* Debug has not LSP number *)
  | Feedback.Info -> hint
  | Feedback.Notice -> information
  | Feedback.Warning -> warning
  | Feedback.Error -> error

let add_message lvl loc msg q =
  let lvl = coq_lvl_to_severity lvl in
  q := (loc, lvl, msg) :: !q

let mk_fb_handler q Feedback.{ contents; _ } =
  match contents with
  | Message (lvl, loc, msg) -> add_message lvl loc msg q
  | _ -> ()

let coq_init opts =
  (* Core Coq initialization *)
  Lib.init ();
  Global.set_impredicative_set false;
  Global.set_native_compiler false;

  if opts.debug then CDebug.set_flags "backtrace";

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  let fb_handler = mk_fb_handler Protect.fb_queue in
  ignore (Feedback.add_feeder fb_handler);

  (* Custom toplevel is used for bytecode-to-js dynlink *)
  let ser_mltop : Mltop.toplevel =
    let open Mltop in
    { load_plugin = opts.load_plugin
    ; load_module = opts.load_module
    ; add_dir = (fun _ -> ())
    ; ml_loop = (fun _ -> ())
    }
  in
  Mltop.set_top ser_mltop;

  (* This should go away in Coq itself *)
  Safe_typing.allow_delayed_constants := true;

  (**************************************************************************)
  (* Add root state!!                                                       *)
  (**************************************************************************)
  Vernacstate.freeze_full_state () |> State.of_coq

(* End of core initialization *)

(**************************************************************************)
(* Per-document, internal Coq initialization                              *)
(**************************************************************************)

(* Inits the context for a document *)
let doc_init ~root_state ~workspace ~uri () =
  (* Lsp.Io.log_error "init" "starting"; *)
  Vernacstate.unfreeze_full_state (State.to_coq root_state);

  (* Set load paths from workspace info. *Important*, this has to happen before
     we declare the library below as [Declaremods/Library] will infer the module
     name by looking at the load path! *)
  Workspace.apply ~uri workspace;

  (* We return the state at this point! *)
  Vernacstate.freeze_full_state () |> State.of_coq

let doc_init ~root_state ~workspace ~uri =
  Protect.eval ~f:(doc_init ~root_state ~workspace ~uri) ()
