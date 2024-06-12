(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

open Interp

let do_handle ~fn ~token action =
  match action with
  | Action.Now handler -> handler ~token
  | Action.Doc { uri; handler } ->
    let open Coq.Compat.Result.O in
    let* doc = fn ~token ~uri |> of_pet_err in
    handler ~token ~doc

let request ~fn ~token ~id ~method_ ~params =
  let do_handle = do_handle ~fn in
  let unhandled () =
    (* JSON-RPC method not found *)
    let code = -32601 in
    let message = "method not found" in
    Error (code, message)
  in
  match handle_request ~do_handle ~unhandled ~token ~method_ ~params with
  | Ok result -> Lsp.Base.Response.mk_ok ~id ~result
  | Error (code, message) -> Lsp.Base.Response.mk_error ~id ~code ~message

type doc_handler =
     token:Coq.Limits.Token.t
  -> uri:Lang.LUri.File.t
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
