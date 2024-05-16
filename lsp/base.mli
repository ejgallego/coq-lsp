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
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* XXX: EJGA This should be an structured value (object or array) *)
module Params : sig
  type t =
    | Dict of (string * Yojson.Safe.t) list
    | Array of Yojson.Safe.t list
end

module Notification : sig
  type t =
    { method_ : string
    ; params : Params.t option
    }
  [@@deriving to_yojson]

  val make : method_:string -> ?params:Params.t -> unit -> t
end

module Request : sig
  type t =
    { id : int
    ; method_ : string
    ; params : Params.t option
    }
  [@@deriving to_yojson]

  val make : method_:string -> id:int -> ?params:Params.t -> unit -> t
end

(* Request response *)
module Response : sig
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
  [@@deriving to_yojson]

  (** Answer to a request *)
  val mk_ok : id:int -> result:Yojson.Safe.t -> t

  (** Fail a request *)
  val mk_error : id:int -> code:int -> message:string -> t

  val id : t -> int
end

(** Basic JSON-RPC Incoming Messages *)
module Message : sig
  type t =
    | Notification of Notification.t
    | Request of Request.t
    | Response of Response.t
  [@@deriving yojson]
end

(** Build request *)

(** Progress *)
module ProgressToken : sig
  type t =
    | String of string
    | Int of int
  [@@deriving yojson]
end

module ProgressParams : sig
  type 'a t =
    { token : ProgressToken.t
    ; value : 'a
    }
  [@@deriving yojson]
end

val mk_progress :
  token:ProgressToken.t -> value:'a -> ('a -> Yojson.Safe.t) -> Yojson.Safe.t

module WorkDoneProgressBegin : sig
  type t =
    { kind : string
    ; title : string
    ; cancellable : bool option [@None]
    ; message : string option [@None]
    ; percentage : int option [@None]
    }
  [@@deriving to_yojson]
end

module WorkDoneProgressReport : sig
  type t =
    { kind : string
    ; cancellable : bool option [@None]
    ; message : string option [@None]
    ; percentage : int option [@None]
    }
  [@@deriving to_yojson]
end

module WorkDoneProgressEnd : sig
  type t = { kind : string } [@@deriving to_yojson]
end
