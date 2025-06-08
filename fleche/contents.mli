(************************************************************************)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)
(* Flèche => document manager: Document Contents                        *)
(************************************************************************)

type t = private
  { raw : string
        (** That's the original, unprocessed document text, including markdown *)
  ; text : string
        (** That's the text to be sent to the prover, already processed, and
            stripped from markdown, encoded in UTF-8 *)
  ; last : Lang.Point.t
        (** Last point of [text], you can derive n_lines from here *)
  ; lines : string Array.t  (** [text] split in lines *)
  }

module R : sig
  type 'a t = private
    | Ok of 'a
    | Error of string
        (** We want to replace the string by a proper diagnostic we can send to
            the client *)

  val map : f:('a -> 'b) -> 'a t -> 'b t
end

(** Process contents *)
val make : uri:Lang.LUri.File.t -> raw:string -> t R.t

(** Make an object of type [t] but don't process the text, this is only used
    internally to still provide some contents when [make] fails. *)
val make_raw : raw:string -> t

(** [extract_raw contents ~range] Returns the sub-string of the [raw] part of
    the document *)
val extract_raw : contents:t -> range:Lang.Range.t -> string
