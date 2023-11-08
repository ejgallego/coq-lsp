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

  let err_code = -32803

  (* We log feedback generated during requests, improve so clients can use this,
     but it needs conversion of positions. *)
  let do_feedback feedback = Fleche.Io.Log.feedback feedback

  let print_err ~name e =
    match e with
    | Coq.Protect.Error.Anomaly (_loc, msg) | User (_loc, msg) ->
      Format.asprintf "Error in %s request: %a" name Pp.pp_with msg

  let of_execution ~name ~f x : t =
    let Coq.Protect.E.{ r; feedback } = f x in
    do_feedback feedback;
    match r with
    | Interrupted -> Error (err_code, name ^ " request interrupted")
    | Completed (Error e) ->
      let error_msg = print_err ~name e in
      Error (err_code, error_msg)
    | Completed (Ok r) -> r
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
    | PosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        ; handler : position
        }

  (* Debug printing *)
  let data fmt = function
    | DocRequest { uri = _; handler = _ } -> Format.fprintf fmt "{k:doc}"
    | PosRequest { uri = _; point; version; postpone; handler = _ } ->
      Format.fprintf fmt "{k:pos | l: %d, c: %d v: %a p: %B}" (fst point)
        (snd point)
        Format.(pp_print_option pp_print_int)
        version postpone

  let dm_request pr =
    match pr with
    | DocRequest { uri; handler = _ } -> Fleche.Theory.Request.(FullDoc { uri })
    | PosRequest { uri; point; version; postpone; handler = _ } ->
      Fleche.Theory.Request.(PosInDoc { uri; point; version; postpone })

  let serve ~doc pr =
    match pr with
    | DocRequest { uri = _; handler } -> handler ~doc
    | PosRequest { uri = _; point; version = _; postpone = _; handler } ->
      handler ~point ~doc
end

let empty ~doc:_ ~point:_ = Ok (`List [])
