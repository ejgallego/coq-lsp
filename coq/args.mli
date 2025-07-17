(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq arguments API                     *)
(*************************************************************************)

open Cmdliner

val coqlib : String.t Term.t
val findlib_config : String.t option Term.t
val ocamlpath : String.t list Term.t
val rload_paths : Loadpath.vo_path List.t Term.t
val qload_paths : Loadpath.vo_path List.t Term.t
val debug : Bool.t Term.t
val bt : Bool.t Term.t
val ri_from : (string option * string) list Term.t
val int_backend : Limits.backend option Term.t
val roots : string list Term.t
val coq_diags_level : int Term.t

(* Internal, used by pet-server, should go away *)
val coqlib_dyn : string
