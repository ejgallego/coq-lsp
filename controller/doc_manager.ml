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

  let doc_table : (Lang.LUri.File.t, t) Hashtbl.t = Hashtbl.create 39

  let create ~uri ~doc =
    (match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ ->
      LIO.trace "do_open"
        ("file "
        ^ Lang.LUri.File.to_string_uri uri
        ^ " not properly closed by client"));
    Hashtbl.add doc_table uri
      { doc; cp_requests = Int.Set.empty; pt_requests = [] }

  let close ~uri = Hashtbl.remove doc_table uri
  let find_opt ~uri = Hashtbl.find_opt doc_table uri

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
    | Failed _ | FailedPermanent _ -> (handle, Int.Set.empty)

  (* trigger pending incremental requests *)
  let update_doc_info ~handle ~(doc : Fleche.Doc.t) =
    let handle, requests = do_requests ~doc ~handle in
    Hashtbl.replace doc_table doc.uri handle;
    requests
end

let diags_of_doc doc =
  List.concat_map Fleche.Doc.Node.diags doc.Fleche.Doc.nodes

let send_diags ~ofn ~doc =
  let diags = diags_of_doc doc in
  let diags =
    Lsp.JLang.mk_diagnostics ~uri:doc.uri ~version:doc.version diags
  in
  ofn diags

let send_perf_data ~ofn ~(doc : Fleche.Doc.t) =
  match doc.completed with
  | Yes _ ->
    let params = Perf.make doc in
    Lsp.Base.mk_notification ~method_:"$/coq/filePerfData" ~params |> ofn
  | _ -> ()

let completed ~(doc : Fleche.Doc.t) =
  match doc.completed with
  | Yes _ | Failed _ | FailedPermanent _ -> true
  | Stopped _ -> false

module Check : sig
  val schedule : uri:Lang.LUri.File.t -> unit
  val deschedule : uri:Lang.LUri.File.t -> unit

  val maybe_check :
    ofn:(Yojson.Safe.t -> unit) -> concise: bool -> (Int.Set.t * Fleche.Doc.t) option
end = struct
  let pending = ref None

  let get_check_target pt_requests =
    let target_of_pt_handle (_, (l, c)) = Fleche.Doc.Target.Position (l, c) in
    Option.cata target_of_pt_handle Fleche.Doc.Target.End
      (List.nth_opt pt_requests 0)

  (* Notification handling; reply is optional / asynchronous *)
  let check ~ofn ~concise ~uri =
    LIO.trace "process_queue" "resuming document checking";
    match Handle.find_opt ~uri with
    | Some handle ->
      let target = get_check_target handle.pt_requests in
      let doc = Fleche.Doc.check ~ofn ~target ~doc:handle.doc () in
      let requests = Handle.update_doc_info ~handle ~doc in
      if not concise then
        (send_diags ~ofn ~doc;
         (* Only if completed! *)
         if completed ~doc then send_perf_data ~ofn ~doc);
      (* Only if completed! *)
      if completed ~doc then pending := None;
      Some (requests, doc)
    | None ->
      LIO.trace "Check.check"
        ("file " ^ Lang.LUri.File.to_string_uri uri ^ " not available");
      None

  let maybe_check ~ofn ~concise = Option.bind !pending (fun uri -> check ~ofn ~concise ~uri)
  let schedule ~uri = pending := Some uri

  let deschedule ~uri =
    if Option.compare Lang.LUri.File.compare (Some uri) !pending = 0 then
      pending := None
end

let send_error_permanent_fail ~ofn ~uri ~version message =
  let open Lang in
  let start = Point.{ line = 0; character = 0; offset = 0 } in
  let end_ = Point.{ line = 0; character = 1; offset = 1 } in
  let range = Range.{ start; end_ } in
  let d = Lang.Diagnostic.{ range; severity = 1; message; extra = None } in
  let diags = Lsp.JLang.mk_diagnostics ~uri ~version [ d ] in
  ofn diags

let create ~ofn ~root_state ~workspace ~uri ~raw ~version =
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
    send_error_permanent_fail ~ofn ~uri ~version (Pp.str message)
  | Interrupted -> ()

(* Set this to false for < 8.18, we could parse the version but not worth it. *)
let sane_coq_base_version = true

let sane_coq_branch =
  CString.string_contains ~where:Coq_config.version ~what:"+lsp"

(* for testing in master, set this to true *)
let force_single_mode = false

let sane_coq_version =
  (sane_coq_base_version || sane_coq_branch) && not force_single_mode

(* Can't wait for the day this goes away *)
let tainted = ref false

let create ~ofn ~root_state ~workspace ~uri ~raw ~version =
  if !tainted && not sane_coq_version then (
    (* Error due to Coq bug *)
    let message =
      "You have opened two or more Coq files simultaneously in the server\n\
       Unfortunately Coq's < 8.18 doesn't properly support that setup yet\n\
       You'll need to close all files but one, and restart the server.\n\n\
       Check coq-lsp webpage (Working with multiple files section) for\n\
       instructions on how to install a fixed branch for earlier Coq versions."
    in
    LIO.logMessage ~lvl:1 ~message;
    (match
       Fleche.Doc.create_failed_permanent ~state:root_state ~uri ~raw ~version
     with
    | Fleche.Contents.R.Error _e -> ()
    | Ok doc -> Handle.create ~uri ~doc);
    send_error_permanent_fail ~ofn ~uri ~version (Pp.str message))
  else (
    tainted := true;
    create ~ofn ~root_state ~workspace ~uri ~raw ~version)

let change ~ofn ~(doc : Fleche.Doc.t) ~version ~raw =
  let uri = doc.uri in
  LIO.trace "bump file"
    (Lang.LUri.File.to_string_uri uri ^ " / version: " ^ string_of_int version);
  let tb = Unix.gettimeofday () in
  match Fleche.Doc.bump_version ~version ~raw doc with
  | Fleche.Contents.R.Error e ->
    (* Send diagnostics for content conversion *)
    let message = Pp.(str "Error in document conversion: " ++ str e) in
    send_error_permanent_fail ~ofn ~uri ~version message;
    Handle.clear_requests ~uri
  | Fleche.Contents.R.Ok doc ->
    let diff = Unix.gettimeofday () -. tb in
    LIO.trace "bump file took" (Format.asprintf "%f" diff);
    let invalid_reqs = Handle.update_doc_version ~doc in
    Check.schedule ~uri;
    invalid_reqs

let change ~ofn ~uri ~version ~raw =
  match Handle.find_opt ~uri with
  | None ->
    LIO.trace "DocHandle.find"
      ("file " ^ Lang.LUri.File.to_string_uri uri ^ " not available");
    Int.Set.empty
  | Some { doc; _ } ->
    if version > doc.version then change ~ofn ~doc ~version ~raw
    else
      (* That's a weird case, get got changes without a version bump? Do nothing
         for now *)
      Int.Set.empty

let close ~uri =
  (* XXX: Our handling of the "queue" is not good, handle should take care of
     that as to avoid desync between the queue and the handle table. *)
  Check.deschedule ~uri;
  Handle.close ~uri

module Request = struct
  type request =
    | FullDoc of { uri : Lang.LUri.File.t }
    | PosInDoc of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        }

  type t =
    { id : int
    ; request : request
    }

  type action =
    | Now of Fleche.Doc.t
    | Postpone
    | Cancel

  let with_doc ~f ~uri =
    match Handle.find_opt ~uri with
    | None ->
      LIO.trace "Request.add"
        ("document " ^ Lang.LUri.File.to_string_uri uri ^ " not available");
      (* XXX Should be cancelled *)
      Cancel
    | Some { doc; _ } -> f doc

  let request_in_range ~(doc : Fleche.Doc.t) ~version (line, col) =
    let in_range =
      match doc.completed with
      | Yes _ -> true
      | Failed range | FailedPermanent range | Stopped range ->
        Fleche.Doc.Target.reached ~range (line, col)
    in
    let in_range =
      match version with
      | None -> in_range
      | Some version -> doc.version >= version && in_range
    in
    in_range

  (** Add a request to be served; returns [true] if request is added to the
      queue , [false] if the request can be already answered. *)
  let add { id; request } =
    match request with
    | FullDoc { uri } ->
      with_doc ~uri ~f:(fun doc ->
          if completed ~doc then Now doc
          else (
            Handle.attach_cp_request ~uri ~id;
            Postpone))
    | PosInDoc { uri; point; version; postpone } ->
      with_doc ~uri ~f:(fun doc ->
          let in_range = request_in_range ~doc ~version point in
          match (in_range, postpone) with
          | true, _ -> Now doc
          | false, true ->
            Handle.attach_pt_request ~uri ~id ~point;
            Postpone
          | false, false -> Cancel)

  (** Removes the request from the list of things to wake up *)
  let remove { id; request } =
    match request with
    | FullDoc { uri } -> Handle.remove_cp_request ~uri ~id
    | PosInDoc { uri; point; _ } -> Handle.remove_pt_request ~uri ~id ~point
end
