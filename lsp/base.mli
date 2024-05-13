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

(** Basic JSON-RPC Incoming Messages *)
module Message : sig
  type t =
    | Notification of
        { method_ : string
        ; params : (string * Yojson.Safe.t) list
        }
    | Request of
        { id : int
        ; method_ : string
        ; params : (string * Yojson.Safe.t) list
        }

  (** Reify an incoming message *)
  val from_yojson : Yojson.Safe.t -> (t, string) Result.t

  val method_ : t -> string
  val params : t -> (string * Yojson.Safe.t) list
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

  val of_yojson : Yojson.Safe.t -> (t, string) Result.t
end

(** Build request *)
val mk_request :
  method_:string -> id:int -> params:Yojson.Safe.t -> Yojson.Safe.t

(** Build notification *)
val mk_notification : method_:string -> params:Yojson.Safe.t -> Yojson.Safe.t

(** Answer to a request *)
val mk_reply : id:int -> result:Yojson.Safe.t -> Yojson.Safe.t

(** Fail a request *)
val mk_request_error : id:int -> code:int -> message:string -> Yojson.Safe.t

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
