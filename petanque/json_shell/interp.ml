open Protocol
module A = Petanque.Agent

let do_request ~token (module R : Request.S) ~id ~params =
  match R.Params.of_yojson (`Assoc params) with
  | Ok params -> (
    match R.handler ~token params with
    | Ok result ->
      let result = R.Response.to_yojson result in
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
  | s when String.equal Init.method_ s ->
    do_request ~token (module Init) ~id ~params
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

let interp ~token (r : Lsp.Base.Message.t) : Yojson.Safe.t option =
  match r with
  | Request { id; method_; params } ->
    let response = handle_request ~token ~id ~method_ ~params in
    let response = Lsp.Base.Response.to_yojson response in
    Some response
  | Notification { method_ = _; params = _ } -> None
  | Response _ ->
    (* XXX: to implement *)
    None
