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
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Info : sig
  type 'a t =
    { res : 'a
    ; goal : Pp.t Goals.reified_goal Goals.goals option
    ; feedback : Pp.t Loc.located list
    }
end

type 'a interp_result = 'a Info.t Protect.R.t

val interp :
     st:State.t
  -> fb_queue:Pp.t Loc.located list ref
  -> Ast.t
  -> State.t interp_result

val marshal_in : (in_channel -> 'a) -> in_channel -> 'a interp_result

val marshal_out :
  (out_channel -> 'a -> unit) -> out_channel -> 'a interp_result -> unit
