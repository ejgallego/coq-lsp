(************************************************************************)
(* Coq Language Server Protocol -- Document                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

val request :
     ast:bool
  -> goals:Rq_goals.format option
  -> unit
  -> (Yojson.Safe.t, string) Request.document

(* Used by coq/getDocument *)
