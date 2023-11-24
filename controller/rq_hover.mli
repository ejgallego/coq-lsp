(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

val hover : Request.position

open Fleche

module Handler : sig
  (** Returns [Some markdown] if there is some hover to match *)
  type 'node h_node =
    contents:Contents.t -> point:int * int -> node:'node -> string option

  type h_doc =
    doc:Doc.t -> point:int * int -> node:Doc.Node.t option -> string option

  (** Many use cases could be grouped into a hook that would pass an
      [Identifier_context.] object, containing the object, its location,
      documentation, and some other relevant information.

      For now we provide hooks for node inspection, contents inspection, and
      document (usually TOC + contents) inspection. *)
  type t =
    | MaybeNode : Doc.Node.t option h_node -> t
    | WithNode : Doc.Node.t h_node -> t
    | WithDoc : h_doc -> t
end

(** Register a hover plugin *)
module Register : sig
  val add : Handler.t -> unit
end
