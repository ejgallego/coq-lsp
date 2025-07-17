(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2018-2025 Shachar Itzhaky Technion -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Javascript utilities                   *)
(*************************************************************************)

open Js_of_ocaml

(* Object to Yojson converter *)
val obj_to_json : < .. > Js.t -> Yojson.Safe.t
val json_to_obj : Yojson.Safe.t -> < .. > Js.t
