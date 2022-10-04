(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type t =
  { range : Types.Range.t
  ; text : String.t
  }

val make : contents:String.t -> loc:Loc.t -> t

(** [find ~offset span] finds an identifier at offset, offset is absolutely
    positioned *)
val find : offset:int -> t -> string
