(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t

(** Builds and URI from a string, like the ones present in the LSP protocol wire *)
val of_string : string -> t

(** Checks if a URI points to a (local) file *)
val is_file_path : t -> bool

(** Uris that are filesystem paths *)
module File : sig
  type uri = t
  type t

  val of_uri : uri -> (t, string) Result.t

  (** Extension, with the dot included *)
  val extension : t -> string

  (** Percent-enconded URI as string *)
  val to_string_uri : t -> string

  (** Filename version, fit for OS functions *)
  val to_string_file : t -> string

  (** compare *)
  val compare : t -> t -> int

  (** equal *)
  val equal : t -> t -> bool

  (** hash *)
  val hash : t -> int
end
