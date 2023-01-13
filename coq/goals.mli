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
  { names : Names.Id.t list
  ; def : 'a option
  ; ty : 'a
  }

type info =
  { evar : Evar.t
  ; name : Names.Id.t option
  }

type 'a reified_goal =
  { info : info
  ; ty : 'a
  ; hyps : 'a hyp list
  }

type 'a goals =
  { goals : 'a list
  ; stack : ('a list * 'a list) list
  ; bullet : Pp.t option
  ; shelf : 'a list
  ; given_up : 'a list
  }

type reified_pp = Pp.t reified_goal goals

(** Stm-independent goal processor *)
val reify :
     ppx:(Environ.env -> Evd.evar_map -> EConstr.t -> 'a)
  -> State.Proof.t
  -> 'a reified_goal goals
