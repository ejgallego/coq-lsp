(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq parsing API                       *)
(*************************************************************************)

module Parsable : sig
  type t

  val make : ?loc:Loc.t -> (unit, char) Gramlib.Stream.t -> t
  val loc : t -> Loc.t
end

val parse :
     token:Limits.Token.t
  -> st:State.t
  -> Parsable.t
  -> (Ast.t option, Loc.t) Protect.E.t

val discard_to_dot : Parsable.t -> unit
