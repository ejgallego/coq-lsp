open Protocol
open Protocol_shell
module A = Petanque.Agent

let do_request ~token (module R : Request.S) ~id ~params =
  match R.Handler.Params.of_yojson (`Assoc params) with
  | Ok params -> (
    match R.Handler.handler ~token params with
    | Ok result ->
      let result = R.Handler.Response.to_yojson result in
      Lsp.Base.Response.mk_ok ~id ~result
    | Error err ->
      let message = A.Error.to_string err in
      let code = A.Error.to_code err in
      Lsp.Base.Response.mk_error ~id ~code ~message)
  | Error message ->
    (* JSON-RPC Parse error *)
    let code = -32700 in
    Lsp.Base.Response.mk_error ~id ~code ~message

let handle_request ~token ~id ~method_ ~params =
  match method_ with
  | s when String.equal SetWorkspace.method_ s ->
    do_request ~token (module SetWorkspace) ~id ~params
  | s when String.equal Start.method_ s ->
    do_request ~token (module Start) ~id ~params
  | s when String.equal RunTac.method_ s ->
    do_request ~token (module RunTac) ~id ~params
  | s when String.equal Goals.method_ s ->
    do_request ~token (module Goals) ~id ~params
  | s when String.equal Premises.method_ s ->
    do_request ~token (module Premises) ~id ~params
  | _ ->
    (* JSON-RPC method not found *)
    let code = -32601 in
    let message = "method not found" in
    Lsp.Base.Response.mk_error ~id ~code ~message

let interp ~token (r : Lsp.Base.Message.t) : Lsp.Base.Message.t option =
  match r with
  | Request { id; method_; params } ->
    let response = handle_request ~token ~id ~method_ ~params in
    Some (Lsp.Base.Message.response response)
  | Notification { method_; params = _ } ->
    let message = "unhandled notification: " ^ method_ in
    let log = Trace.(make Params.{ message; verbose = None }) in
    Some log
  | Response (Ok { id; _ }) | Response (Error { id; _ }) ->
    let message = "unhandled response: " ^ string_of_int id in
    let log = Trace.(make Params.{ message; verbose = None }) in
    Some log
