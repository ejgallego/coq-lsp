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
(* Copyright 2019-2022 Inria -- LGPL 2.1+                               *)
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

val mk_range : Fleche.Types.Range.t -> Yojson.Safe.t

(** Build notification *)
val mk_notification :
  method_:string -> params:(string * Yojson.Safe.t) list -> Yojson.Safe.t

(** Answer to a request *)
val mk_reply : id:int -> result:Yojson.Safe.t -> Yojson.Safe.t

(** Fail a request *)
val mk_request_error : id:int -> code:int -> message:string -> Yojson.Safe.t

(* val mk_diagnostic : Range.t * int * string * unit option -> Yojson.Basic.t *)
val mk_diagnostics :
     uri:string
  -> version:int
  -> (Fleche.Types.Range.t * int * string * unit option) list
  -> Yojson.Safe.t

val std_protocol : bool ref
