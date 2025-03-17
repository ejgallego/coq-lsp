(************************************************************************)
(* Rocq Language Server Protocol                                        *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 EJGA       -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** {1 JSON-RPC input/output} *)

(** Read a JSON-RPC message from channel; [None] signals [EOF] *)
val read_message : in_channel -> (Base.Message.t, string) Result.t option

(** Send a JSON-RPC message to channel *)
val send_message : Format.formatter -> Base.Message.t -> unit
