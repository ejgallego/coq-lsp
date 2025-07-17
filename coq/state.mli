(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq State API                         *)
(*************************************************************************)

type t

val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
val mode : st:t -> Pvernac.proof_mode option
val parsing : st:t -> Vernacstate.Parser.t

(** Proof states *)
module Proof : sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
  val to_coq : t -> Vernacstate.LemmaStack.t
end

val lemmas : st:t -> Proof.t option
val program : st:t -> Declare.OblState.View.t Names.Id.Map.t

(** Execute a command in state [st]. Unfortunately this can produce anomalies as
    Coq state setting is imperative, so we need to wrap it in protect. *)
val in_state :
  token:Limits.Token.t -> st:t -> f:('a -> 'b) -> 'a -> ('b, Loc.t) Protect.E.t

(** Execute a monadic command in state [st]. *)
val in_stateM :
     token:Limits.Token.t
  -> st:t
  -> f:('a -> ('b, Loc.t) Protect.E.t)
  -> 'a
  -> ('b, Loc.t) Protect.E.t

(** Drop the top proof from the state *)
val drop_proof : st:t -> t

(** Drop all proofs from the state *)
val drop_all_proofs : st:t -> t

(** Fully admit an ongoing proof *)
val admit : token:Limits.Token.t -> st:t -> (t, Loc.t) Protect.E.t

(** Admit the current sub-goal *)
val admit_goal : token:Limits.Token.t -> st:t -> (t, Loc.t) Protect.E.t

(** Info about universes *)
val info_universes :
  token:Limits.Token.t -> st:t -> (int * int, Loc.t) Protect.E.t

(** Extra / interanl *)
val marshal_in : in_channel -> t

val marshal_out : out_channel -> t -> unit
val of_coq : Vernacstate.t -> t
val to_coq : t -> Vernacstate.t
