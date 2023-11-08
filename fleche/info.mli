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
(* Copyright (C) 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+  *)
(* Copyright (C) 2019-2022 Emilio J. Gallego Arias, INRIA               *)
(* Copyright (C) 2022-2022 Shachar Itzhaky, Technion                    *)
(************************************************************************)

(* Some issues due to different API in clients... *)
module type Point = sig
  type t

  val in_range : ?range:Lang.Range.t -> t -> bool
  val gt_range : ?range:Lang.Range.t -> t -> bool

  (** [to_offset] will help to resolve a position from for example (line,col) to
      an offset, but in some case requires a lookup method. *)
  type offset_table = string

  val to_offset : t -> offset_table -> int
  val to_string : t -> string
end

module LineCol : Point with type t = int * int
module Offset : Point with type t = int

type approx =
  | Exact  (** Exact on point *)
  | PrevIfEmpty  (** If no match, return prev *)
  | Prev  (** If no match, return prev, if match, too *)

(** Located queries *)
module type S = sig
  module P : Point

  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  val node : (approx, Doc.Node.t) query
end

module LC : S with module P := LineCol
module O : S with module P := Offset

(** We move towards a more modular design here, for preprocessing *)
module Goals : sig
  val goals :
    st:Coq.State.t -> (Pp.t Coq.Goals.reified_pp option, Loc.t) Coq.Protect.E.t

  val program : st:Coq.State.t -> Declare.OblState.View.t Names.Id.Map.t
end

module Completion : sig
  val candidates :
    st:Coq.State.t -> string -> (string list option, Loc.t) Coq.Protect.E.t
end
