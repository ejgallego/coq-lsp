(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Std

type pp_tag =
  [%import: Pp.pp_tag]
  [@@deriving sexp,yojson,hash,compare]

type block_type =
  [%import: Pp.block_type]
  [@@deriving sexp,yojson,hash,compare]

module P = struct
  type t = Pp.t
  type _t =
  | Pp_empty
  | Pp_string of string
  | Pp_glue of _t list
  | Pp_box  of block_type * _t
  | Pp_tag  of pp_tag * _t
  (* Are those redundant? *)
  | Pp_print_break of int * int
  | Pp_force_newline
  | Pp_comment of string list
  [@@deriving sexp,yojson,hash,compare]

  open Pp

  let rec of_t (d : t) : _t = match repr d with
  | Ppcmd_empty -> Pp_empty
  | Ppcmd_string s -> Pp_string s
  | Ppcmd_glue l -> Pp_glue (List.map of_t l)
  | Ppcmd_box (bt,d) -> Pp_box(bt, of_t d)
  | Ppcmd_tag (t,d) -> Pp_tag(t, of_t d)
  | Ppcmd_print_break (n,m) -> Pp_print_break(n,m)
  | Ppcmd_force_newline -> Pp_force_newline
  | Ppcmd_comment s -> Pp_comment s

  let rec to_t (d : _t) : t = unrepr (match d with
  | Pp_empty -> Ppcmd_empty
  | Pp_string s -> Ppcmd_string s
  | Pp_glue l -> Ppcmd_glue (List.map to_t l)
  | Pp_box (bt,d) -> Ppcmd_box(bt, to_t d)
  | Pp_tag (t,d) -> Ppcmd_tag(t, to_t d)
  | Pp_print_break (n,m) -> Ppcmd_print_break(n,m)
  | Pp_force_newline -> Ppcmd_force_newline
  | Pp_comment s -> Ppcmd_comment s)

end

include SerType.Biject(P)

type doc_view =
  [%import: Pp.doc_view]
  [@@deriving sexp,yojson,hash,compare]
