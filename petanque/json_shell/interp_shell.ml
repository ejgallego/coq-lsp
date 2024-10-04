(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

open Petanque_json.Interp
open Protocol_shell

let do_handle ~fn ~token action =
  match action with
  | Action.Now handler -> handler ~token
  | Action.Doc { uri; contents; handler } ->
    let open Coq.Compat.Result.O in
    let* doc = fn ~token ~uri ~contents |> of_pet_err in
    handler ~token ~doc

let request ~fn ~token ~id ~method_ ~params =
  let unhandled ~token ~method_ =
    match method_ with
    | s when String.equal SetWorkspace.method_ s ->
      do_handle ~fn ~token (do_request (module SetWorkspace) ~params)
    | s when String.equal TableOfContents.method_ s ->
      do_handle ~fn ~token (do_request (module TableOfContents) ~params)
    | _ ->
      (* JSON-RPC method not found *)
      let code = -32601 in
      let message = Format.asprintf "method %s not found" method_ in
      Error (code, message)
  in
  let do_handle = do_handle ~fn in
  match handle_request ~do_handle ~unhandled ~token ~method_ ~params with
  | Ok result -> Lsp.Base.Response.mk_ok ~id ~result
  | Error (code, message) -> Lsp.Base.Response.mk_error ~id ~code ~message

type doc_handler =
     token:Coq.Limits.Token.t
  -> uri:Lang.LUri.File.t
  -> contents:string option
  -> (Fleche.Doc.t, Petanque.Agent.Error.t) Result.t

let interp ~fn ~token (r : Lsp.Base.Message.t) : Lsp.Base.Message.t option =
  match r with
  | Request { id; method_; params } ->
    let response = request ~fn ~token ~id ~method_ ~params in
    Some (Lsp.Base.Message.response response)
  | Notification { method_; params = _ } ->
    let message = "unhandled notification: " ^ method_ in
    let log = Lsp.Io.mk_logTrace ~message ~extra:None in
    Some (Lsp.Base.Message.Notification log)
  | Response (Ok { id; _ }) | Response (Error { id; _ }) ->
    let message = "unhandled response: " ^ string_of_int id in
    let log = Lsp.Io.mk_logTrace ~message ~extra:None in
    Some (Lsp.Base.Message.Notification log)
