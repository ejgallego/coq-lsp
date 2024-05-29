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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

(* This file contains some coq-specific commands, we should instead
   functorialize it so we can share with other OCaml-specific tools *)

module J = Yojson.Safe
module U = Yojson.Safe.Util

let int_field name dict = U.to_int List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

module Params = struct
  type t = (string * Yojson.Safe.t) list

  let to_yojson dict = `Assoc dict
end

module Notification = struct
  type t =
    { method_ : string
    ; params : Params.t
    }

  let make ~method_ ~params () = { method_; params }

  let to_yojson { method_; params } =
    let params = [ ("params", Params.to_yojson params) ] in
    `Assoc ([ ("jsonrpc", `String "2.0"); ("method", `String method_) ] @ params)
end

module Request = struct
  type t =
    { id : int
    ; method_ : string
    ; params : Params.t
    }

  let make ~method_ ~id ~params () = { id; method_; params }

  let to_yojson { method_; id; params } =
    let params = [ ("params", Params.to_yojson params) ] in
    `Assoc
      ([ ("jsonrpc", `String "2.0")
       ; ("id", `Int id)
       ; ("method", `String method_)
       ]
      @ params)
end

module Response = struct
  type t =
    | Ok of
        { id : int
        ; result : Yojson.Safe.t
        }
    | Error of
        { id : int
        ; code : int
        ; message : string
        ; data : Yojson.Safe.t option
        }

  let mk_ok ~id ~result = Ok { id; result }
  let mk_error ~id ~code ~message = Error { id; code; message; data = None }

  let id = function
    | Ok { id; _ } | Error { id; _ } -> id

  let to_yojson = function
    | Ok { id; result } ->
      `Assoc [ ("jsonrpc", `String "2.0"); ("id", `Int id); ("result", result) ]
    | Error { id; code; message; data = _ } ->
      `Assoc
        [ ("jsonrpc", `String "2.0")
        ; ("id", `Int id)
        ; ("error", `Assoc [ ("code", `Int code); ("message", `String message) ])
        ]
end

module Message = struct
  type t =
    | Notification of Notification.t
    | Request of Request.t
    | Response of Response.t

  let response_of_yojson dict =
    let id = int_field "id" dict in
    match List.assoc_opt "error" dict with
    | None ->
      let result = List.assoc "result" dict in
      Response.Ok { id; result }
    | Some error ->
      let error = U.to_assoc error in
      let code = int_field "code" error in
      let message = string_field "message" error in
      let data = None in
      Error { id; code; message; data }

  let request_of_yojson method_ dict =
    let params =
      List.assoc_opt "params" dict |> Option.map U.to_assoc |> Option.default []
    in
    match List.assoc_opt "id" dict with
    | None -> Notification { Notification.method_; params }
    | Some id ->
      let id = U.to_int id in
      Request { Request.id; method_; params }

  let of_yojson msg =
    let dict = U.to_assoc msg in
    match List.assoc_opt "method" dict with
    | None -> Response (response_of_yojson dict)
    | Some method_ -> request_of_yojson (U.to_string method_) dict

  let of_yojson msg =
    try of_yojson msg |> Result.ok with
    | Not_found -> Error ("missing parameter: " ^ J.to_string msg)
    | U.Type_error (msg, obj) ->
      Error (Format.asprintf "msg: %s; obj: %s" msg (J.to_string obj))

  let to_yojson = function
    | Notification n -> Notification.to_yojson n
    | Request r -> Request.to_yojson r
    | Response r -> Response.to_yojson r
end

module ProgressToken : sig
  type t =
    | String of string
    | Int of int
  [@@deriving yojson]
end = struct
  type t =
    | String of string
    | Int of int

  let of_yojson x =
    match x with
    | `String s -> Result.ok (String s)
    | `Int i -> Result.ok (Int i)
    | _ -> Result.error "failure to parse ProgressToken.t"

  let to_yojson = function
    | String s -> `String s
    | Int i -> `Int i
end

module ProgressParams = struct
  type 'a t =
    { token : ProgressToken.t
    ; value : 'a
    }
  [@@deriving yojson]
end

let mk_progress ~token ~value f =
  let params = ProgressParams.(to_yojson f { token; value }) in
  let params = U.to_assoc params in
  Notification.(to_yojson { method_ = "$/progress"; params })

module WorkDoneProgressBegin = struct
  type t =
    { kind : string
    ; title : string
    ; cancellable : bool option [@None]
    ; message : string option [@None]
    ; percentage : int option [@None]
    }
  [@@deriving to_yojson]
end

module WorkDoneProgressReport = struct
  type t =
    { kind : string
    ; cancellable : bool option [@None]
    ; message : string option [@None]
    ; percentage : int option [@None]
    }
  [@@deriving to_yojson]
end

module WorkDoneProgressEnd = struct
  type t = { kind : string } [@@deriving to_yojson]
end
