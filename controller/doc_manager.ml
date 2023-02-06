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
    ; cp_requests : Int.Set.t
          (* For now we just store the request id to wake up on completion,
             later on we may want to store a more interesting type, for example
             "wake up when a location is reached", or always to continue the
             streaming *)
    ; pt_requests : (int * (int * int)) list (* id, point *)
    }

  let pt_eq (id1, (l1, c1)) (id2, (l2, c2)) = id1 = id2 && l1 = l2 && c1 = c2

  let pt_gt x y =
    let lx, cx = x in
    let ly, cy = y in
    lx > ly || (lx = ly && cx > cy)

  let doc_table : (string, t) Hashtbl.t = Hashtbl.create 39

  let create ~uri ~doc =
    (match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ ->
      LIO.trace "do_open" ("file " ^ uri ^ " not properly closed by client"));
    Hashtbl.add doc_table uri
      { doc; cp_requests = Int.Set.empty; pt_requests = [] }

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

  let pt_ids l = List.map (fun (id, _) -> id) l |> Int.Set.of_list

  (* Clear requests *)
  let clear_requests ~uri =
    match Hashtbl.find_opt doc_table uri with
    | None -> Int.Set.empty
    | Some { cp_requests; pt_requests; doc } ->
      let invalid_reqs = Int.Set.union cp_requests (pt_ids pt_requests) in
      Hashtbl.replace doc_table uri
        { doc; cp_requests = Int.Set.empty; pt_requests = [] };
      invalid_reqs

  (* Clear requests and update doc *)
  let update_doc_version ~(doc : Fleche.Doc.t) =
    let invalid_reqs = clear_requests ~uri:doc.uri in
    Hashtbl.replace doc_table doc.uri
      { doc; cp_requests = Int.Set.empty; pt_requests = [] };
    invalid_reqs

  let map_cp_requests ~uri ~f =
    match Hashtbl.find_opt doc_table uri with
    | Some { doc; cp_requests; pt_requests } ->
      let cp_requests = f cp_requests in
      Hashtbl.replace doc_table uri { doc; cp_requests; pt_requests }
    | None -> ()

  let attach_cp_request ~uri ~id =
    let f cp_requests = Int.Set.add id cp_requests in
    map_cp_requests ~uri ~f

  let remove_cp_request ~uri ~id =
    let f cp_requests = Int.Set.remove id cp_requests in
    map_cp_requests ~uri ~f

  let map_pt_requests ~uri ~f =
    match Hashtbl.find_opt doc_table uri with
    | Some { doc; cp_requests; pt_requests } ->
      let pt_requests = f pt_requests in
      Hashtbl.replace doc_table uri { doc; cp_requests; pt_requests }
    | None -> ()

  (* This needs to be insertion sort! *)
  let pt_insert x xs = CList.insert pt_gt x xs

  let attach_pt_request ~uri ~id ~point =
    let f pt_requests = pt_insert (id, point) pt_requests in
    map_pt_requests ~uri ~f

  let remove_pt_request ~uri ~id ~point =
    let f pt_requests = CList.remove pt_eq (id, point) pt_requests in
    map_pt_requests ~uri ~f

  (* For now only on completion, I think we want check to return the list of
     requests that can be served / woken up *)
  let do_requests ~doc ~handle =
    let handle = { handle with doc } in
    match doc.completed with
    | Yes _ ->
      let pt_ids = pt_ids handle.pt_requests in
      let wake_up = Int.Set.union pt_ids handle.cp_requests in
      let pt_requests = [] in
      let cp_requests = Int.Set.empty in
      ({ handle with cp_requests; pt_requests }, wake_up)
    | Stopped range ->
      let fullfilled, delayed =
        List.partition
          (fun (_id, point) -> Fleche.Doc.Target.reached ~range point)
          handle.pt_requests
      in
      let handle = { handle with pt_requests = delayed } in
      (handle, pt_ids fullfilled)
    | Failed _ -> (handle, Int.Set.empty)

  (* trigger pending incremental requests *)
  let update_doc_info ~handle ~(doc : Fleche.Doc.t) =
    let handle, requests = do_requests ~doc ~handle in
    Hashtbl.replace doc_table doc.uri handle;
    requests
end

let diags_of_doc doc =
  List.concat_map Fleche.Doc.Node.diags doc.Fleche.Doc.nodes

let send_diags ~ofmt ~doc =
  let diags = diags_of_doc doc in
  let diags =
    Lsp.JLang.mk_diagnostics ~uri:doc.uri ~version:doc.version diags
  in
  LIO.send_json ofmt @@ diags

module Check = struct
  let pending = ref None

  let get_check_target pt_requests =
    let target_of_pt_handle (_, (l, c)) = Fleche.Doc.Target.Position (l, c) in
    Option.cata target_of_pt_handle Fleche.Doc.Target.End
      (List.nth_opt pt_requests 0)

  let completed ~(doc : Fleche.Doc.t) =
    match doc.completed with
    | Yes _ | Failed _ -> true
    | Stopped _ -> false

  (* Notification handling; reply is optional / asynchronous *)
  let check ~ofmt ~uri =
    LIO.trace "process_queue" "resuming document checking";
    match Handle.find_opt ~uri with
    | Some handle ->
      let target = get_check_target handle.pt_requests in
      let doc = Fleche.Doc.check ~ofmt ~target ~doc:handle.doc () in
      let requests = Handle.update_doc_info ~handle ~doc in
      send_diags ~ofmt ~doc;
      (* Only if completed! *)
      if completed ~doc then pending := None;
      requests
    | None ->
      LIO.trace "Check.check" ("file " ^ uri ^ " not available");
      Int.Set.empty

  let maybe_check ~ofmt = Option.map (fun uri -> check ~ofmt ~uri) !pending
  let schedule ~uri = pending := Some uri
end

let send_error_permanent_fail ~ofmt ~uri ~version message =
  let open Lang in
  let start = Point.{ line = 0; character = 0; offset = 0 } in
  let end_ = Point.{ line = 0; character = 1; offset = 1 } in
  let range = Range.{ start; end_ } in
  let d = Lang.Diagnostic.{ range; severity = 0; message; extra = None } in
  let diags = Lsp.JLang.mk_diagnostics ~uri ~version [ d ] in
  LIO.send_json ofmt @@ diags

let create ~ofmt ~root_state ~workspace ~uri ~raw ~version =
  let r = Fleche.Doc.create ~state:root_state ~workspace ~uri ~raw ~version in
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
    LIO.logMessage ~lvl:1 ~message;
    send_error_permanent_fail ~ofmt ~uri ~version (Pp.str message)
  | Interrupted -> ()

(* Can't wait for the day this goes away *)
let tainted = ref false

let create ~ofmt ~root_state ~workspace ~uri ~raw ~version =
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
  create ~ofmt ~root_state ~workspace ~uri ~raw ~version

let change ~ofmt ~(doc : Fleche.Doc.t) ~version ~raw =
  let uri = doc.uri in
  LIO.trace "bump file" (uri ^ " / version: " ^ string_of_int version);
  let tb = Unix.gettimeofday () in
  match Fleche.Doc.bump_version ~version ~raw doc with
  | Fleche.Contents.R.Error e ->
    (* Send diagnostics for content conversion *)
    let message = Pp.(str "Error in document conversion: " ++ str e) in
    send_error_permanent_fail ~ofmt ~uri ~version message;
    Handle.clear_requests ~uri
  | Fleche.Contents.R.Ok doc ->
    let diff = Unix.gettimeofday () -. tb in
    LIO.trace "bump file took" (Format.asprintf "%f" diff);
    let invalid_reqs = Handle.update_doc_version ~doc in
    Check.schedule ~uri;
    invalid_reqs

let change ~ofmt ~uri ~version ~raw =
  match Handle.find_opt ~uri with
  | None ->
    LIO.trace "DocHandle.find" ("file " ^ uri ^ " not available");
    Int.Set.empty
  | Some { doc; _ } ->
    if version > doc.version then change ~ofmt ~doc ~version ~raw
    else
      (* That's a weird case, get got changes without a version bump? Do nothing
         for now *)
      Int.Set.empty

let close = Handle.close
let find_doc = Handle.find_doc
let add_on_completion ~uri ~id = Handle.attach_cp_request ~uri ~id
let remove_on_completion ~uri ~id = Handle.remove_cp_request ~uri ~id
let add_on_point ~uri ~id ~point = Handle.attach_pt_request ~uri ~id ~point
let remove_on_point ~uri ~id ~point = Handle.remove_pt_request ~uri ~id ~point
