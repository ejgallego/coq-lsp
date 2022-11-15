(************************************************************************)
(* Flèche Document Manager                                              *)
(* License: LGPL 2.1 / GPL3+                                            *)
(* Copyright (C) 2016-2019 MINES ParisTech                              *)
(* Copyright (C) 2019-2022 Inria                                        *)
(* Copyright (C) 2022-2022 Shachar Itzhaky, Technion Institute of Tech  *)
(************************************************************************)

(* Some issues due to different API in clients... *)
module type Point = sig
  type t

  val in_range : ?loc:Lang.Loc.t -> t -> bool
  val gt_range : ?loc:Lang.Loc.t -> t -> bool

  (** [to_offset] will help to resolve a position from for example (line,col) to
      an offset, but in some case requires a lookup method. *)
  type offset_table = string

  val to_offset : t -> offset_table -> int
  val to_string : t -> string
end

module LineCol : Point with type t = int * int
module Offset : Point with type t = int

type approx =
  | Exact
  | PickPrev

(** Located queries *)
module type S = sig
  module P : Point

  type ('a, 'r) query = doc:Doc.t -> point:P.t -> 'a -> 'r option

  val goals : (approx, Coq.Goals.reified_pp) query
  val info : (approx, string) query
  val completion : (string, string list) query
end

module LC : S with module P := LineCol
module O : S with module P := Offset
