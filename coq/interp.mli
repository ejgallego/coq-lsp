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

(** Intepretation of "pure" Coq commands, that is to say, commands that are
    assumed not to interact with the file-system, etc... Note these commands
    will be memoized. *)
val interp :
  token:Limits.Token.t -> st:State.t -> Ast.t -> (State.t, Loc.t) Protect.E.t

(** Interpretation of "require". We wrap this function for two reasons:

    - to make the read-effect dependency explicit
    - to workaround the lack of a pure interface in Coq *)
module Require : sig
  val interp :
       token:Limits.Token.t
    -> st:State.t
    -> Files.t
    -> Ast.Require.t
    -> (State.t, Loc.t) Protect.E.t
end
