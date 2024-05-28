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

type 'a hyp =
  { names : string list  (** This will become [Names.Id.t list] in 0.2.0 *)
  ; def : 'a option
  ; ty : 'a
  }

type info =
  { evar : Evar.t
  ; name : Names.Id.t option
  }

type 'a reified_goal =
  { info : info
  ; hyps : 'a hyp list
  ; ty : 'a
  }

val map_reified_goal : f:('a -> 'b) -> 'a reified_goal -> 'b reified_goal

type ('a, 'pp) goals =
  { goals : 'a list
  ; stack : ('a list * 'a list) list
  ; bullet : 'pp option
  ; shelf : 'a list
  ; given_up : 'a list
  }

val map_goals :
  f:('a -> 'b) -> g:('pp -> 'pp') -> ('a, 'pp) goals -> ('b, 'pp') goals

type 'pp reified_pp = ('pp reified_goal, 'pp) goals

(** Stm-independent goal processor *)
val reify :
     ppx:(Environ.env -> Evd.evar_map -> EConstr.t -> 'pp)
  -> State.Proof.t
  -> ('pp reified_goal, Pp.t) goals
