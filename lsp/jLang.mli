(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Point : sig
  type t = Lang.Point.t [@@deriving yojson]
end

module Range : sig
  type t = Lang.Range.t [@@deriving yojson]
end

val mk_diagnostics :
  uri:string -> version:int -> Lang.Diagnostic.t list -> Yojson.Safe.t
