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

let string_field name dict = U.to_string List.(assoc name dict)

let odict_field ~default name dict =
  Option.cata U.to_assoc default (List.assoc_opt name dict)

module Message = struct
  type t =
    | Notification of
        { method_ : string [@key "method"]
        ; params : (string * Yojson.Safe.t) list
        }
    | Request of
        { id : int
        ; method_ : string [@key "method"]
        ; params : (string * Yojson.Safe.t) list
        }

  (** Reify an incoming message *)
  let from_yojson msg =
    try
      let dict = U.to_assoc msg in
      let method_ = string_field "method" dict in
      let params = odict_field ~default:[] "params" dict in
      (match List.assoc_opt "id" dict with
      | None -> Notification { method_; params }
      | Some id ->
        let id = U.to_int id in
        Request { id; method_; params })
      |> Result.ok
    with
    | Not_found -> Error ("missing parameter: " ^ J.to_string msg)
    | U.Type_error (msg, obj) ->
      Error (Format.asprintf "msg: %s; obj: %s" msg (J.to_string obj))

  let method_ = function
    | Notification { method_; _ } | Request { method_; _ } -> method_

  let params = function
    | Notification { params; _ } | Request { params; _ } -> params
end

let mk_reply ~id ~result =
  `Assoc [ ("jsonrpc", `String "2.0"); ("id", `Int id); ("result", result) ]

let mk_request_error ~id ~code ~message =
  `Assoc
    [ ("jsonrpc", `String "2.0")
    ; ("id", `Int id)
    ; ("error", `Assoc [ ("code", `Int code); ("message", `String message) ])
    ]

let mk_notification ~method_ ~params =
  `Assoc
    [ ("jsonrpc", `String "2.0")
    ; ("method", `String method_)
    ; ("params", params)
    ]

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
  mk_notification ~method_:"$/progress" ~params

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
