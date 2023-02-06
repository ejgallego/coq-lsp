(************************************************************************)
(* Flèche => document manager: Document Contents                        *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t = private
  { raw : string
        (** That's the original, unprocessed document text, including markdown *)
  ; text : string
        (** That's the text to be sent to the prover, already processed, and
            stripped from markdown, encoded in UTF-8 *)
  ; last : Types.Point.t
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

val make : uri:string -> raw:string -> t R.t
