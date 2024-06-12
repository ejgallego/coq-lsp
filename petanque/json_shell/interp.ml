open Protocol
open Protocol_shell
module A = Petanque.Agent

(* These types ares basically duplicated with controller/request.ml; move to a
   common lib (lsp?) *)
type 'a r = ('a, int * string) Result.t

module Action = struct
  type 'a t =
    | Now of (token:Coq.Limits.Token.t -> Yojson.Safe.t r)
    | Doc of
        { uri : Lang.LUri.File.t
        ; handler :
            token:Coq.Limits.Token.t -> doc:Fleche.Doc.t -> Yojson.Safe.t r
        }
end
(* End of controller/request.ml *)

let of_pet_err res =
  Result.map_error
    (fun err ->
      let message = Petanque.Agent.Error.to_string err in
      let code = Petanque.Agent.Error.to_code err in
      (code, message))
    res

(* Basically a functor from R.Handler.t to Action.t, but closing over params *)
let do_request (module R : Protocol.Request.S) ~params =
  let of_pet res = Result.map R.Handler.Response.to_yojson res |> of_pet_err in
  let handler params =
    match R.Handler.handler with
    | Immediate handler ->
      Action.Now (fun ~token -> handler ~token params |> of_pet)
    | FullDoc { uri_fn; handler } ->
      let uri = uri_fn params in
      let handler ~token ~doc = handler ~token ~doc params |> of_pet in
      Action.Doc { uri; handler }
  in
  match R.Handler.Params.of_yojson (`Assoc params) with
  | Ok params -> handler params
  | Error message ->
    (* JSON-RPC Parse error *)
    let code = -32700 in
    Action.Now (fun ~token:_ -> Error (code, message))

type 'a handle =
     token:Coq.Limits.Token.t
  -> (module Protocol.Request.S)
  -> params:(string * Yojson.Safe.t) list
  -> 'a

let handle_request ~(do_handle : 'a handle) ~unhandled ~token ~method_ ~params =
  match method_ with
  | s when String.equal SetWorkspace.method_ s ->
    do_handle ~token (module SetWorkspace) ~params
  | s when String.equal Start.method_ s ->
    do_handle ~token (module Start) ~params
  | s when String.equal RunTac.method_ s ->
    do_handle ~token (module RunTac) ~params
  | s when String.equal Goals.method_ s ->
    do_handle ~token (module Goals) ~params
  | s when String.equal Premises.method_ s ->
    do_handle ~token (module Premises) ~params
  | _ -> unhandled ()

let do_handle ~fn ~token (module R : Protocol.Request.S) ~params =
  match do_request (module R) ~params with
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
