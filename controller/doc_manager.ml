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
    ; requests : Int.Set.t
          (* For now we just store the request id to wake up on completion,
             later on we may want to store a more interesting type, for example
             "wake up when a location is reached", or always to continue the
             streaming *)
    }

  let doc_table : (string, t) Hashtbl.t = Hashtbl.create 39

  let create ~uri ~doc =
    (match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ ->
      LIO.trace "do_open" ("file " ^ uri ^ " not properly closed by client"));
    Hashtbl.add doc_table uri { doc; requests = Int.Set.empty }

  let close ~uri = Hashtbl.remove doc_table uri

  let find ~uri =
    match Hashtbl.find_opt doc_table uri with
    | Some h -> h
    | None ->
      LIO.trace "DocHandle.find" ("file " ^ uri ^ " not available");
      raise AbortRequest

  let find_opt ~uri = Hashtbl.find_opt doc_table uri
  let find_doc ~uri = (find ~uri).doc

  let _update_doc ~handle ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { handle with doc }

  (* Clear requests *)
  let update_doc_version ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { doc; requests = Int.Set.empty }

  let attach_request ~uri ~id =
    match Hashtbl.find_opt doc_table uri with
    | Some { doc; requests } ->
      let requests = Int.Set.add id requests in
      Hashtbl.replace doc_table uri { doc; requests }
    | None -> ()

  (* For now only on completion, I think we want check to return the list of
     requests that can be served / woken up *)
  let do_requests ~doc ~handle =
    let handle = { handle with doc } in
    match doc.completed with
    | Yes _ -> ({ doc; requests = Int.Set.empty }, handle.requests)
    | Stopped _ -> (handle, Int.Set.empty)
    | Failed _ -> (handle, Int.Set.empty)

  (* trigger pending incremental requests *)
  let update_doc_info ~handle ~(doc : Fleche.Doc.t) =
    let handle, requests = do_requests ~doc ~handle in
    Hashtbl.replace doc_table doc.uri handle;
    requests
end

let diags_of_doc doc =
  List.concat_map Fleche.Doc.Node.diags doc.Fleche.Doc.nodes

module Check = struct
  let pending = ref None

  let completed ~uri =
    let doc = Handle.find_doc ~uri in
    match doc.completed with
    | Yes _ | Failed _ -> true
    | Stopped _ -> false

  (* Notification handling; reply is optional / asynchronous *)
  let check ofmt ~uri =
    LIO.trace "process_queue" "resuming document checking";
    match Handle.find_opt ~uri with
    | Some handle ->
      let doc = Fleche.Doc.check ~ofmt ~doc:handle.doc () in
      let requests = Handle.update_doc_info ~handle ~doc in
      let diags = diags_of_doc doc in
      let diags =
        Lsp_util.lsp_of_diags ~uri:doc.uri ~version:doc.version diags
      in
      LIO.send_json ofmt @@ diags;
      (* Only if completed! *)
      if completed ~uri then pending := None;
      requests
    | None ->
      LIO.trace "Check.check" ("file " ^ uri ^ " not available");
      Int.Set.empty

  let check_or_yield ~ofmt =
    match !pending with
    | None ->
      Thread.delay 0.1;
      Int.Set.empty
    | Some uri -> check ofmt ~uri

  let schedule ~uri = pending := Some uri
end

let create ~root_state ~workspace ~uri ~contents ~version =
  let r =
    Fleche.Doc.create ~state:root_state ~workspace ~uri ~contents ~version
  in
  match r with
  | Completed (Result.Ok doc) ->
    Handle.create ~uri ~doc;
    Check.schedule ~uri
  | Completed (Result.Error (Anomaly (_, msg)))
  | Completed (Result.Error (User (_, msg))) ->
    (* For now we inform the user of the problem, we could be finer and create a
       ghost node for the implicit import, but we will phase that out in Coq
       upstream at some point. *)
    let message =
      Format.asprintf "Fleche.Doc.create, internal error: @[%a@]" Pp.pp_with msg
    in
    LIO.logMessage ~lvl:1 ~message
  | Interrupted -> ()

(* Can't wait for the day this goes away *)
let tainted = ref false

let create ~root_state ~workspace ~uri ~contents ~version =
  if !tainted then
    (* Warn about Coq bug *)
    let message =
      "You have opened two or more Coq files simultaneously in the server\n\
       Unfortunately Coq's parser doesn't properly support that setup yet\n\
       If you see some strange parsing errors please close all files but one\n\
       Then restart the coq-lsp server; sorry for the inconveniencies"
    in
    LIO.logMessage ~lvl:2 ~message
  else tainted := true;
  create ~root_state ~workspace ~uri ~contents ~version

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
let serve_on_completion ~uri ~id = Handle.attach_request ~uri ~id
