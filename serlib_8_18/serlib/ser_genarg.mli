(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

(* val sexp_of_raw_tactic_expr : (Tacexpr.raw_tactic_expr -> Sexp.t) ref *)
(* val sexp_of_tacdef_body     : (Tacexpr.tacdef_body     -> Sexp.t) ref *)

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

type rlevel = Genarg.rlevel
  [@@deriving sexp,yojson,hash,compare]
type glevel = Genarg.glevel
  [@@deriving sexp,yojson,hash,compare]
type tlevel = Genarg.tlevel
  [@@deriving sexp,yojson,hash,compare]

type 'a generic_argument = 'a Genarg.generic_argument
  [@@deriving sexp,yojson,hash,compare]

type glob_generic_argument = Genarg.glob_generic_argument
[@@deriving sexp,yojson,hash,compare]

type raw_generic_argument = Genarg.raw_generic_argument
[@@deriving sexp,yojson,hash,compare]

type typed_generic_argument = Genarg.typed_generic_argument
val typed_generic_argument_of_sexp : Sexp.t -> Genarg.typed_generic_argument
val sexp_of_typed_generic_argument : Genarg.typed_generic_argument -> Sexp.t

(* Registering serializing functions *)
type ('raw, 'glb, 'top) gen_ser =
  { raw_ser : 'raw -> Sexp.t
  ; raw_des : Sexp.t -> 'raw
  ; raw_hash : 'raw Ppx_hash_lib.Std.Hash.folder
  ; raw_compare : 'raw -> 'raw -> int

  ; glb_ser : 'glb -> Sexp.t
  ; glb_des : Sexp.t -> 'glb
  ; glb_hash : 'glb Ppx_hash_lib.Std.Hash.folder
  ; glb_compare : 'glb -> 'glb -> int

  ; top_ser : 'top -> Sexp.t
  ; top_des : Sexp.t -> 'top
  ; top_hash : 'top Ppx_hash_lib.Std.Hash.folder
  ; top_compare : 'top -> 'top -> int
  }

val register_genser :
  ('raw, 'glb, 'top) Genarg.genarg_type ->
  ('raw, 'glb, 'top) gen_ser -> unit

val gen_ser_pair :
  ('raw1, 'glb1, 'top1) gen_ser ->
  ('raw2, 'glb2, 'top2) gen_ser ->
  (('raw1 * 'raw2), ('glb1 * 'glb2), ('top1 * 'top2)) gen_ser

val gen_ser_list :
  ('raw, 'glb, 'top) gen_ser ->
  ('raw list, 'glb list, 'top list) gen_ser

val mk_uniform : ('t -> Sexp.t) -> (Sexp.t -> 't) ->
  't Ppx_hash_lib.Std.Hash.folder ->
  't Ppx_compare_lib.compare ->
  ('t,'t,'t) gen_ser

module type GenSer0 = sig
  type t [@@deriving sexp,hash,compare]
end

module GS0 (M : GenSer0) : sig val genser : (M.t,M.t,M.t) gen_ser end

module type GenSer = sig
  type raw [@@deriving sexp,hash,compare]
  type glb [@@deriving sexp,hash,compare]
  type top [@@deriving sexp,hash,compare]
end

module GS (M : GenSer) : sig val genser : (M.raw,M.glb,M.top) gen_ser end
