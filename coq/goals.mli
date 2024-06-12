(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin SERAPI                                  *)
(* Copyright 2016-2019 MINES ParisTech -- LGPL 2.1+                     *)
(* Copyright 2019-2022 Inria           -- LGPL 2.1+                     *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Reified_goal : sig
  type 'a hyp =
    { names : string list  (** This will become [Names.Id.t list] in 0.2.0 *)
    ; def : 'a option
    ; ty : 'a
    }

  type info =
    { evar : Evar.t
    ; name : Names.Id.t option
    }

  type 'a t =
    { info : info
    ; hyps : 'a hyp list
    ; ty : 'a
    }

  val map : f:('a -> 'b) -> 'a t -> 'b t
  val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
end

type ('a, 'pp) t =
  { goals : 'a list
  ; stack : ('a list * 'a list) list
  ; bullet : 'pp option
  ; shelf : 'a list
  ; given_up : 'a list
  }

val equal :
     ('a -> 'a -> bool)
  -> ('pp -> 'pp -> bool)
  -> ('a, 'pp) t
  -> ('a, 'pp) t
  -> bool

val map : f:('a -> 'b) -> g:('pp -> 'pp') -> ('a, 'pp) t -> ('b, 'pp') t

type 'pp reified_pp = ('pp Reified_goal.t, 'pp) t

(** Stm-independent goal processor *)
val reify :
     ppx:(Environ.env -> Evd.evar_map -> EConstr.t -> 'pp)
  -> State.Proof.t
  -> ('pp Reified_goal.t, Pp.t) t

(* equality functions with heuristics *)
module Equality : sig
  (** Goal-based eq heuristic, will return [true] when goals are "equal", in a
      proof search sense *)
  val equal_goals : State.Proof.t -> State.Proof.t -> bool
end
