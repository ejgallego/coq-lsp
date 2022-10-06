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

module Info = struct
  type 'a t =
    { res : 'a
    ; feedback : Message.t list
    }
end

let get_feedback fb_queue =
  let res = !fb_queue in
  fb_queue := [];
  res

type 'a interp_result = 'a Info.t Protect.R.t

let coq_interp ~st cmd =
  let st = State.to_coq st in
  let cmd = Ast.to_coq cmd in
  Vernacinterp.interp ~st cmd |> State.of_coq

let interp ~st ~fb_queue cmd =
  Protect.eval cmd ~f:(fun cmd ->
      let res = coq_interp ~st cmd in
      (* It is safe to call the printer here as the state is guaranteed to be
         the right one after `coq_interp`, but beware! *)
      let feedback = List.rev @@ get_feedback fb_queue in
      { Info.res; feedback })

let marshal_out f oc res =
  match res with
  | Protect.R.Interrupted -> ()
  | Protect.R.Completed res -> (
    match res with
    | Ok res ->
      Marshal.to_channel oc 0 [];
      f oc res.Info.res
    | Error (loc, msg) ->
      Marshal.to_channel oc 1 [];
      Marshal.to_channel oc loc [];
      Marshal.to_channel oc msg [];
      ())

let marshal_in f ic =
  let tag : int = Marshal.from_channel ic in
  if tag = 0 then
    let res = f ic in
    Protect.R.Completed (Ok { Info.res; feedback = [] })
  else
    let loc : Loc.t option = Marshal.from_channel ic in
    let msg : Pp.t = Marshal.from_channel ic in
    Protect.R.Completed (Error (loc, msg))
