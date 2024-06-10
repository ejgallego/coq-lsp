open Protocol
open Protocol_shell
module A = Petanque.Agent

let do_request ~token (module R : Protocol.Request.S) ~params =
  match R.Handler.Params.of_yojson (`Assoc params) with
  | Ok params -> (
    match R.Handler.handler ~token params with
    | Ok result -> Ok (R.Handler.Response.to_yojson result)
    | Error err ->
      let message = Petanque.Agent.Error.to_string err in
      let code = Petanque.Agent.Error.to_code err in
      Error (code, message))
  | Error message ->
    (* JSON-RPC Parse error *)
    let code = -32700 in
    Error (code, message)

let handle_request ~token ~method_ ~params =
  match method_ with
  | s when String.equal SetWorkspace.method_ s ->
    do_request ~token (module SetWorkspace) ~params
  | s when String.equal Start.method_ s ->
    do_request ~token (module Start) ~params
  | s when String.equal RunTac.method_ s ->
    do_request ~token (module RunTac) ~params
  | s when String.equal Goals.method_ s ->
    do_request ~token (module Goals) ~params
  | s when String.equal Premises.method_ s ->
    do_request ~token (module Premises) ~params
  | _ ->
    (* JSON-RPC method not found *)
    let code = -32601 in
    let message = "method not found" in
    Error (code, message)

let request ~token ~id ~method_ ~params =
  match handle_request ~token ~method_ ~params with
  | Ok result -> Lsp.Base.Response.mk_ok ~id ~result
  | Error (code, message) -> Lsp.Base.Response.mk_error ~id ~code ~message

let interp ~token (r : Lsp.Base.Message.t) : Lsp.Base.Message.t option =
  match r with
  | Request { id; method_; params } ->
    let response = request ~token ~id ~method_ ~params in
    Some (Lsp.Base.Message.response response)
  | Notification { method_; params = _ } ->
    let message = "unhandled notification: " ^ method_ in
    let log = Lsp.Io.mk_logTrace ~message ~extra:None in
    Some (Lsp.Base.Message.Notification log)
  | Response (Ok { id; _ }) | Response (Error { id; _ }) ->
    let message = "unhandled response: " ^ string_of_int id in
    let log = Lsp.Io.mk_logTrace ~message ~extra:None in
    Some (Lsp.Base.Message.Notification log)
