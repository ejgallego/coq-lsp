(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type format =
  | Pp
  | Str
  | Box

(** [goals ~pp_format ?pretac] Serve goals at point; users can request
    pre-processing and formatting using the provided parameters. *)
val goals :
     pp_format:format
  -> mode:Fleche.Info.approx
  -> pretac:string option
  -> unit
  -> (Yojson.Safe.t, string) Request.position

(** For printing of goals in [coq/getDocument] *)
val pp : pp_format:format -> Yojson.Safe.t Fleche.Info.Goals.printer
