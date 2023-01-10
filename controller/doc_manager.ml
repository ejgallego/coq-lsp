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
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module LIO = Lsp.Io

(* XXX: We need to handle this better *)
exception AbortRequest

(* Handler for document *)
module Handle = struct
  type t =
    { doc : Fleche.Doc.t
    ; requests : unit (* placeholder for requests attached to a document *)
    }

  let doc_table : (string, t) Hashtbl.t = Hashtbl.create 39

  let create ~uri ~doc =
    (match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ ->
      LIO.trace "do_open" ("file " ^ uri ^ " not properly closed by client"));
    Hashtbl.add doc_table uri { doc; requests = () }

  let close ~uri = Hashtbl.remove doc_table uri

  let find ~uri =
    match Hashtbl.find_opt doc_table uri with
    | Some h -> h
    | None ->
      LIO.trace "DocHandle.find" ("file " ^ uri ^ " not available");
      raise AbortRequest

  let find_opt ~uri = Hashtbl.find_opt doc_table uri
  let find_doc ~uri = (find ~uri).doc

  let _update ~handle ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { handle with doc }

  (* Clear requests *)
  let update_doc_version ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { doc; requests = () }

  (* trigger pending incremental requests *)
  let update_doc_info ~handle ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { handle with doc }
end

let diags_of_doc doc =
  List.concat_map (fun node -> node.Fleche.Doc.diags) doc.Fleche.Doc.nodes

module Check = struct
  let pending = ref None

  let completed ~uri =
    let doc = Handle.find_doc ~uri in
    match doc.completed with
    | Yes _ | Failed _ -> true
    | Stopped _ -> false

  (* Notification handling; reply is optional / asynchronous *)
  let check ofmt ~fb_queue ~uri =
    LIO.trace "process_queue" "resuming document checking";
    match Handle.find_opt ~uri with
    | Some handle ->
      let doc = Fleche.Doc.check ~ofmt ~doc:handle.doc ~fb_queue in
      Handle.update_doc_info ~handle ~doc;
      let diags = diags_of_doc doc in
      let diags =
        Lsp_util.lsp_of_diags ~uri:doc.uri ~version:doc.version diags
      in
      LIO.send_json ofmt @@ diags;
      (* Only if completed! *)
      if completed ~uri then pending := None
    | None ->
      LIO.trace "Check.check" ("file " ^ uri ^ " not available");
      ()

  let check_or_yield ofmt ~fb_queue =
    match !pending with
    | None -> Thread.delay 0.1
    | Some uri -> check ofmt ~fb_queue ~uri

  let schedule ~uri = pending := Some uri
end

let create ~root_state ~workspace ~uri ~contents ~version =
  match
    Fleche.Doc.create ~state:root_state ~workspace ~uri ~contents ~version
  with
  | Coq.Protect.R.Completed (Result.Ok doc) ->
    Handle.create ~uri ~doc;
    Check.schedule ~uri
  (* Maybe send some diagnostics in this case? *)
  | Coq.Protect.R.Completed (Result.Error (Anomaly (_, msg)))
  | Coq.Protect.R.Completed (Result.Error (User (_, msg))) ->
    let msg = Pp.string_of_ppcmds msg in
    LIO.trace "Fleche.Doc.create" ("internal error" ^ msg)
  | Coq.Protect.R.Interrupted -> ()

let change ~uri ~version ~contents =
  let doc = Handle.find_doc ~uri in
  if version > doc.version then (
    LIO.trace "bump file" (uri ^ " / version: " ^ string_of_int version);
    let tb = Unix.gettimeofday () in
    let doc = Fleche.Doc.bump_version ~version ~contents doc in
    let diff = Unix.gettimeofday () -. tb in
    LIO.trace "bump file took" (Format.asprintf "%f" diff);
    let () = Handle.update_doc_version ~doc in
    Check.schedule ~uri)
  else
    (* That's a weird case, get got changes without a version bump? Do nothing
       for now *)
    ()

let close = Handle.close
let find_doc = Handle.find_doc
