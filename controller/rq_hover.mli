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
  type 'node h =
    contents:Contents.t -> point:int * int -> node:'node -> string option

  type t =
    | MaybeNode : Doc.Node.t option h -> t
    | WithNode : Doc.Node.t h -> t
end

(** Register a hover plugin *)
module Register : sig
  val add : Handler.t -> unit
end
