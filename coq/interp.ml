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

let hc : (Names.DirPath.t, Library.library_t) Hashtbl.t = Hashtbl.create 1000

let use_cache = true

let intern dp =
  if use_cache then
    match Hashtbl.find_opt hc dp with
    | Some lib -> lib
    | None ->
      let lib_resolver = Loadpath.try_locate_absolute_library in
      let lib = Library.intern_from_file ~lib_resolver dp in
      let () = Hashtbl.add hc dp lib in
      lib
  else
      let lib_resolver = Loadpath.try_locate_absolute_library in
      Library.intern_from_file ~lib_resolver dp

let coq_interp ~st cmd =
  let st = State.to_coq st in
  let cmd = Ast.to_coq cmd in
  Vernacinterp.interp ~intern ~st cmd |> State.of_coq

let interp ~st cmd = Protect.eval cmd ~f:(coq_interp ~st)

module Require = struct
  (* We could improve this Coq upstream by making the API a bit more
     orthogonal *)
  let interp ~st _files
      { Ast.Require.from; export; mods; loc = _; attrs; control } =
    let () = Vernacstate.unfreeze_full_state (State.to_coq st) in
    let fn () = Vernacentries.vernac_require ~intern from export mods in
    (* Check generic attributes *)
    let fn () =
      Synterp.with_generic_atts ~check:true attrs (fun ~atts ->
          (* Fail if attributes are not empty *)
          Attributes.unsupported_attributes atts;
          fn ())
    in
    (* Execute control commands *)
    let () = Utils.with_control ~fn ~control ~st in
    Vernacstate.freeze_full_state () |> State.of_coq

  let interp ~st files cmd = Protect.eval ~f:(interp ~st files) cmd
end
