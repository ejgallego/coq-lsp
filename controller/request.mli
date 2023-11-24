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
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module R : sig
  type t = (Yojson.Safe.t, int * string) Result.t

  (* We don't allow to pass the feedback to the [f] handler yet, that's not
     hard, but I'd suggest waiting until the conversion of character points is
     working better. *)
  val of_execution :
    name:string -> f:('a -> (t, Loc.t) Coq.Protect.E.t) -> 'a -> t
end

type document = doc:Fleche.Doc.t -> R.t
type position = doc:Fleche.Doc.t -> point:int * int -> R.t

(** Requests that require data access *)
module Data : sig
  type t =
    | DocRequest of
        { uri : Lang.LUri.File.t
        ; handler : document
        }
    | PosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        ; handler : position
        }

  (* Debug printing *)
  val data : Format.formatter -> t -> unit
  val dm_request : t -> Fleche.Theory.Request.request
  val serve : doc:Fleche.Doc.t -> t -> R.t
end

(** Returns an empty list of results for any position / document *)
val empty : position
