(************************************************************************)
(* Coq Petanque                                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(************************************************************************)

open Protocol
module A = Petanque.Agent

(* These types ares basically duplicated with controller/request.ml; move to a
   common lib (lsp?) *)
type 'a r = ('a, int * string) Result.t

module Action = struct
  type t =
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

type 'a handle = token:Coq.Limits.Token.t -> Action.t -> 'a

let handle_request ~(do_handle : 'a handle) ~unhandled ~token ~method_ ~params =
  match method_ with
  | s when String.equal Start.method_ s ->
    do_handle ~token (do_request (module Start) ~params)
  | s when String.equal RunTac.method_ s ->
    do_handle ~token (do_request (module RunTac) ~params)
  | s when String.equal Goals.method_ s ->
    do_handle ~token (do_request (module Goals) ~params)
  | s when String.equal Premises.method_ s ->
    do_handle ~token (do_request (module Premises) ~params)
  | s when String.equal StateEqual.method_ s ->
    do_handle ~token (do_request (module StateEqual) ~params)
  | s when String.equal StateHash.method_ s ->
    do_handle ~token (do_request (module StateHash) ~params)
  | _ -> unhandled ~token ~method_
