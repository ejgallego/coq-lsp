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
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module R = struct
  type t = (Yojson.Safe.t, int * string) Result.t
end

type document = doc:Fleche.Doc.t -> R.t
type position = doc:Fleche.Doc.t -> point:int * int -> R.t

(** Requests that require data access *)
module Data = struct
  type t =
    | DocRequest of
        { uri : Lang.LUri.File.t
        ; handler : document
        }
    | IntDocRequest of
        { uri : Lang.LUri.File.t
        ; handler : token:Limits.Token.t -> document
        }
    | PosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        ; handler : position
        }
    | IntPosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        ; handler : token:Limits.Token.t -> position
        }

  (* Debug printing *)
  let data fmt = function
    | DocRequest { uri = _; handler = _ }
    | IntDocRequest { uri = _; handler = _ } -> Format.fprintf fmt "{k:doc}"
    | PosRequest { uri = _; point; version; postpone; handler = _ }
    | IntPosRequest { uri = _; point; version; postpone; handler = _ } ->
      Format.fprintf fmt "{k:pos | l: %d, c: %d v: %a p: %B}" (fst point)
        (snd point)
        Format.(pp_print_option pp_print_int)
        version postpone

  let dm_request pr =
    match pr with
    | DocRequest { uri; handler = _ } | IntDocRequest { uri; handler = _ } ->
      Doc_manager.Request.(FullDoc { uri })
    | PosRequest { uri; point; version; postpone; handler = _ }
    | IntPosRequest { uri; point; version; postpone; handler = _ } ->
      Doc_manager.Request.(PosInDoc { uri; point; version; postpone })

  let serve ~token ~doc pr =
    match pr with
    | DocRequest { uri = _; handler } -> handler ~doc
    | IntDocRequest { uri = _; handler } -> handler ~token ~doc
    | PosRequest { uri = _; point; version = _; postpone = _; handler } ->
      handler ~point ~doc
    | IntPosRequest { uri = _; point; version = _; postpone = _; handler } ->
      handler ~token ~point ~doc
end
