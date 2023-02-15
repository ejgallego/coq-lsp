(************************************************************************)
(* Coq Language Server Protocol -- Common requests routines             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

val get_id_at_point : doc:Fleche.Doc.t -> point:int * int -> string option
