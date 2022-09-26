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
(* Copyright (C) 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+  *)
(* Copyright (C) 2019-2022 Emilio J. Gallego Arias, INRIA               *)
(* Copyright (C) 2022-2022 Shachar Itzhaky, Technion                    *)
(************************************************************************)

module G = Serapi.Serapi_goals

val get_goals_line_col :
  doc:Coq_doc.t -> point:int * int -> Pp.t G.reified_goal G.ser_goals option

type approx =
  | Exact
  | PickPrev

val get_goals_point :
     doc:Coq_doc.t
  -> point:int
  -> approx:approx
  -> Pp.t G.reified_goal G.ser_goals option
