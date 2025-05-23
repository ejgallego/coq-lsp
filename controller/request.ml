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

module Error = struct
  type 'a t =
    { code : int
    ; payload : 'a
    ; feedback : Lang.Range.t Coq.Message.t list
    }

  let make ?(feedback = []) code payload = { code; payload; feedback }

  let map ~f { code; payload; feedback } =
    let payload = f payload in
    { code; payload; feedback }
end

module R = struct
  type ('r, 'e) t = ('r, 'e Error.t) Result.t

  let map_error ~f = Result.map_error (Error.map ~f)
  let code = -32803

  let print_err ~name e =
    match e with
    | Coq.Protect.Error.Anomaly { msg; _ } | User { msg; _ } ->
      Format.asprintf "Error in %s request: %a" name Pp.pp_with msg

  let of_execution ~lines ~name ~f x : ('r, string) t =
    let Coq.Protect.E.{ r; feedback } = f x in
    let f = Coq.Utils.to_range ~lines in
    let feedback = List.map (Coq.Message.map ~f) feedback in
    match r with
    | Interrupted ->
      let payload = name ^ " request interrupted" in
      Error { code; payload; feedback }
    | Completed (Error e) ->
      let payload = print_err ~name e in
      Error { code; payload; feedback }
    | Completed (Ok r) ->
      (* Fleche.Io.Log.feedback feedback; *)
      r
end

type ('r, 'e) document =
  token:Coq.Limits.Token.t -> doc:Fleche.Doc.t -> ('r, 'e) R.t

type ('r, 'e) position =
     token:Coq.Limits.Token.t
  -> doc:Fleche.Doc.t
  -> point:int * int
  -> ('r, 'e) R.t

(** Requests that require data access *)
module Data = struct
  type ('r, 'e) t =
    | Immediate of
        { uri : Lang.LUri.File.t
        ; handler : ('r, 'e) document
        }
    | DocRequest of
        { uri : Lang.LUri.File.t
        ; postpone : bool
        ; handler : ('r, 'e) document
        }
    | PosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        ; handler : ('r, 'e) position
        }

  (* Debug printing *)
  let data fmt = function
    | Immediate { uri = _; handler = _ } -> Format.fprintf fmt "{k:imm }"
    | DocRequest { uri = _; postpone; handler = _ } ->
      Format.fprintf fmt "{k:doc | p: %B}" postpone
    | PosRequest { uri = _; point; version; postpone; handler = _ } ->
      Format.fprintf fmt "{k:pos | l: %d, c: %d v: %a p: %B}" (fst point)
        (snd point)
        Format.(pp_print_option pp_print_int)
        version postpone

  let dm_request pr =
    match pr with
    | Immediate { uri; handler = _ } ->
      (uri, false, Fleche.Theory.Request.Immediate)
    | DocRequest { uri; postpone; handler = _ } ->
      (uri, postpone, Fleche.Theory.Request.FullDoc)
    | PosRequest { uri; point; version; postpone; handler = _ } ->
      (uri, postpone, Fleche.Theory.Request.(PosInDoc { point; version }))

  let serve ~token ~doc pr =
    match pr with
    | Immediate { uri = _; handler } -> handler ~token ~doc
    | DocRequest { uri = _; postpone = _; handler } -> handler ~token ~doc
    | PosRequest { uri = _; point; version = _; postpone = _; handler } ->
      handler ~token ~point ~doc
end
