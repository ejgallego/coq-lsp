(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type t =
  { range : Lang.Range.t
  ; contents : String.t
  }

val make : contents:String.t -> range:Lang.Range.t -> t

(** [find ~offset ~range text] finds an identifier at offset, offset is
    absolutely positioned *)
val find : offset:int -> range:Lang.Range.t -> string -> string

(** TODO:

    - We want some kind of tokenization for the span, two kinds of spans, with
      AST, and without *)

(** Focused text span on a range / XXX same structure than caching *)

(**
  type context =
    | Parsed of { span : t; node : Doc.node }
    (** [span] corresponding to [node]  *)
    | Text of { span : t; prev : Doc.node }
    (** Independent [span], [prev] node for help *)
*)
