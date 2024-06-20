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

open Sexplib
open Ppx_hash_lib.Std
open Ppx_compare_lib.Builtin

let hash_tagged f st tag x = let st = Hash.fold_string st tag in f st x
let hash_pair f1 f2 st (x1,x2) = let st = f1 st x1 in f2 st x2

(**********************************************************************)
(* GenArg                                                             *)
(**********************************************************************)

open Genarg

type rlevel =
  [%import: Genarg.rlevel]
  [@@deriving sexp,yojson,hash,compare]
type glevel =
  [%import: Genarg.glevel]
  [@@deriving sexp,yojson,hash,compare]
type tlevel =
  [%import: Genarg.tlevel]
  [@@deriving sexp,yojson,hash,compare]

let rec sexp_of_genarg_type : type a b c. (a, b, c) genarg_type -> Sexp.t = fun gt ->
  match gt with
  | ExtraArg tag   -> List [Atom "ExtraArg"; Atom (ArgT.repr tag)]
  | ListArg rt     -> List [Atom "ListArg"; sexp_of_genarg_type rt]
  | OptArg  rt     -> List [Atom "OptArg";  sexp_of_genarg_type rt]
  | PairArg(t1,t2) -> List [Atom "PairArg"; sexp_of_genarg_type t1; sexp_of_genarg_type t2]

let rec hash_fold_genarg_type : type a b c. (a, b, c) genarg_type Hash.folder = fun st gt ->
  match gt with
  | ExtraArg tag   -> hash_tagged Hash.fold_string st "ExtraArg" (ArgT.repr tag)
  | ListArg rt     -> hash_tagged hash_fold_genarg_type st "ListArg" rt
  | OptArg  rt     -> hash_tagged hash_fold_genarg_type st "OptArg" rt
  | PairArg(t1,t2) -> hash_tagged (hash_pair hash_fold_genarg_type hash_fold_genarg_type) st "PairArg" (t1, t2)

let sexp_of_abstract_argument_type : type lvl. ('o, lvl) abstract_argument_type -> Sexp.t = fun  at ->
  match at with
  | Rawwit w -> List [Atom "Rawwit"; sexp_of_genarg_type w]
  | Glbwit w -> List [Atom "Glbwit"; sexp_of_genarg_type w]
  | Topwit w -> List [Atom "Topwit"; sexp_of_genarg_type w]

let rec argument_type_of_sexp : Sexp.t -> argument_type = fun sexp ->
  match sexp with
  | List [Atom "ExtraArg"; Atom tag] ->
    begin match ArgT.name tag with
      | None              -> raise (Failure "SEXP Exception in argument_type")
      | Some (ArgT.Any t) -> ArgumentType (ExtraArg t)
    end
  | List [Atom "ListArg"; s1] ->
    let (ArgumentType t) = argument_type_of_sexp s1 in
    ArgumentType (ListArg t)
  | List [Atom "OptArg";  s1] ->
    let (ArgumentType t) = argument_type_of_sexp s1 in
    ArgumentType (OptArg t)
  | List [Atom "PairArg"; s1; s2] ->
    let (ArgumentType t1) = argument_type_of_sexp s1 in
    let (ArgumentType t2) = argument_type_of_sexp s2 in
    ArgumentType (PairArg(t1,t2))
  | _ -> raise (Failure "SEXP Exception")

let hash_fold_abstract_argument_type : type lvl. ('o, lvl) abstract_argument_type Hash.folder  = fun st at ->
  match at with
  | Rawwit w -> hash_tagged hash_fold_genarg_type st "raw" w
  | Glbwit w -> hash_tagged hash_fold_genarg_type st "glb" w
  | Topwit w -> hash_tagged hash_fold_genarg_type st "top" w

type ('raw, 'glb, 'top) gen_ser =
  { raw_ser : 'raw -> Sexp.t
  ; raw_des : Sexp.t -> 'raw
  ; raw_hash : 'raw Hash.folder
  ; raw_compare : 'raw -> 'raw -> int

  ; glb_ser : 'glb -> Sexp.t
  ; glb_des : Sexp.t -> 'glb
  ; glb_hash : 'glb Hash.folder
  ; glb_compare : 'glb -> 'glb -> int

  ; top_ser : 'top -> Sexp.t
  ; top_des : Sexp.t -> 'top
  ; top_hash : 'top Ppx_hash_lib.Std.Hash.folder
  ; top_compare : 'top -> 'top -> int
  }

module T2_ = struct
  type ('a, 'b) t = 'a * 'b [@@deriving hash, compare]
end

let gen_ser_list :
  ('raw, 'glb, 'top) gen_ser ->
  ('raw list, 'glb list, 'top list) gen_ser = fun g ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_list g.raw_ser
  ; raw_des = list_of_sexp g.raw_des
  ; raw_hash = Hash.Builtin.hash_fold_list g.raw_hash
  ; raw_compare = compare_list g.raw_compare

  ; glb_ser = sexp_of_list g.glb_ser
  ; glb_des = list_of_sexp g.glb_des
  ; glb_hash = Hash.Builtin.hash_fold_list g.glb_hash
  ; glb_compare = compare_list g.glb_compare

  ; top_ser = sexp_of_list g.top_ser
  ; top_des = list_of_sexp g.top_des
  ; top_hash = Hash.Builtin.hash_fold_list g.top_hash
  ; top_compare = compare_list g.top_compare
  }

let gen_ser_opt :
  ('raw, 'glb, 'top) gen_ser ->
  ('raw option, 'glb option, 'top option) gen_ser = fun g ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_option g.raw_ser
  ; raw_des = option_of_sexp g.raw_des
  ; raw_hash = Hash.Builtin.hash_fold_option g.raw_hash
  ; raw_compare = compare_option g.raw_compare

  ; glb_ser = sexp_of_option g.glb_ser
  ; glb_des = option_of_sexp g.glb_des
  ; glb_hash = Hash.Builtin.hash_fold_option g.glb_hash
  ; glb_compare = compare_option g.glb_compare

  ; top_ser = sexp_of_option g.top_ser
  ; top_des = option_of_sexp g.top_des
  ; top_hash = Hash.Builtin.hash_fold_option g.top_hash
  ; top_compare = compare_option g.top_compare
  }

let gen_ser_pair :
  ('raw1, 'glb1, 'top1) gen_ser ->
  ('raw2, 'glb2, 'top2) gen_ser ->
  (('raw1 * 'raw2), ('glb1 * 'glb2), ('top1 * 'top2)) gen_ser = fun g1 g2 ->
  let open Sexplib.Conv in
  { raw_ser = sexp_of_pair g1.raw_ser g2.raw_ser
  ; raw_des = pair_of_sexp g1.raw_des g2.raw_des
  ; raw_hash = T2_.hash_fold_t g1.raw_hash g2.raw_hash
  ; raw_compare = T2_.compare g1.raw_compare g2.raw_compare

  ; glb_ser = sexp_of_pair g1.glb_ser g2.glb_ser
  ; glb_des = pair_of_sexp g1.glb_des g2.glb_des
  ; glb_hash = T2_.hash_fold_t g1.glb_hash g2.glb_hash
  ; glb_compare = T2_.compare g1.glb_compare g2.glb_compare

  ; top_ser = sexp_of_pair g1.top_ser g2.top_ser
  ; top_des = pair_of_sexp g1.top_des g2.top_des
  ; top_hash = T2_.hash_fold_t g1.top_hash g2.top_hash
  ; top_compare = T2_.compare g1.top_compare g2.top_compare
  }

module SerObj = struct

  type ('raw, 'glb, 'top) obj = ('raw, 'glb, 'top) gen_ser

  let sexp_of_gen typ ga =
    let typ = typ ^ ": " ^ Sexp.to_string (sexp_of_genarg_type ga) in
    Serlib_base.sexp_of_opaque ~typ

  let name = "ser_arg"
  let default _ga =
    Some
      {
        (* raw_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "raw"; sexp_of_genarg_type ga])); *)
        raw_ser = sexp_of_gen "raw" _ga
      ; raw_des = (Sexplib.Conv_error.no_matching_variant_found "raw_arg")
      ; raw_hash = (fun st a -> Hash.fold_int st (Hashtbl.hash a))
      ; raw_compare = Stdlib.compare

      (* glb_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "glb"; sexp_of_genarg_type ga])); *)
      ; glb_ser = sexp_of_gen "glb" _ga
      ; glb_des = (Sexplib.Conv_error.no_matching_variant_found "glb_arg")
      ; glb_hash = (fun st a -> Hash.fold_int st (Hashtbl.hash a))
      ; glb_compare = Stdlib.compare

      (* top_ser = (fun _ -> Sexp.(List [Atom "[XXX ser_gen]"; Atom "top"; sexp_of_genarg_type ga])); *)
      ; top_ser = sexp_of_gen "top" _ga
      ; top_des = (Sexplib.Conv_error.no_matching_variant_found "top_arg")
      ; top_hash = (fun st a -> Hash.fold_int st (Hashtbl.hash a))
      ; top_compare = Stdlib.compare
      }
end

module SerGen = Register(SerObj)
let register_genser ty obj = SerGen.register0 ty obj

let rec get_gen_ser_ty : type r g t. (r,g,t) Genarg.genarg_type -> (r,g,t) gen_ser =
  fun gt -> match gt with
  | Genarg.ExtraArg _      -> SerGen.obj gt
  | Genarg.ListArg  t      -> gen_ser_list (get_gen_ser_ty t)
  | Genarg.OptArg   t      -> gen_ser_opt  (get_gen_ser_ty t)
  | Genarg.PairArg(t1, t2) -> gen_ser_pair (get_gen_ser_ty t1) (get_gen_ser_ty t2)

let get_gen_ser : type lvl. ('o,lvl) abstract_argument_type -> ('o -> 't) = fun aty ->
  match aty with
  | Genarg.Rawwit ty -> (get_gen_ser_ty ty).raw_ser
  | Genarg.Glbwit ty -> (get_gen_ser_ty ty).glb_ser
  | Genarg.Topwit ty -> (get_gen_ser_ty ty).top_ser

let generic_des : type lvl. ('o,lvl) abstract_argument_type -> Sexp.t -> lvl generic_argument = fun ty s ->
  match ty with
  | Genarg.Rawwit w -> GenArg(ty, (get_gen_ser_ty w).raw_des s)
  | Genarg.Glbwit w -> GenArg(ty, (get_gen_ser_ty w).glb_des s)
  | Genarg.Topwit w -> GenArg(ty, (get_gen_ser_ty w).top_des s)

let hash_fold_generic : type lvl. ('o,lvl) abstract_argument_type -> 'o Ppx_hash_lib.Std.Hash.folder = fun aty ->
  match aty with
  | Genarg.Rawwit ty -> (get_gen_ser_ty ty).raw_hash
  | Genarg.Glbwit ty -> (get_gen_ser_ty ty).glb_hash
  | Genarg.Topwit ty -> (get_gen_ser_ty ty).top_hash

let compare_generic : type lvl. ('o,lvl) abstract_argument_type -> 'o Ppx_compare_lib.compare = fun aty ->
  match aty with
  | Genarg.Rawwit ty -> (get_gen_ser_ty ty).raw_compare
  | Genarg.Glbwit ty -> (get_gen_ser_ty ty).glb_compare
  | Genarg.Topwit ty -> (get_gen_ser_ty ty).top_compare

(* We need to generalize this to use the proper printers for opt *)
let mk_sexparg st so =
  Sexp.List [Atom "GenArg"; st; so]

(* XXX: There is still some duplication here in the traversal of g_ty, but
   we can live with that for now.  *)
let sexp_of_genarg_val : type a. a generic_argument -> Sexp.t =
  fun g -> match g with
  | GenArg (g_ty, g_val) ->
    mk_sexparg (sexp_of_abstract_argument_type g_ty) (get_gen_ser g_ty g_val)

let sexp_of_generic_argument : type a. (a -> Sexp.t) -> a generic_argument -> Sexp.t =
  fun _level_tag g ->
  sexp_of_genarg_val g

type rgen_argument = RG : 'lvl generic_argument -> rgen_argument

let hash_fold_genarg_val : type a. a generic_argument Hash.folder =
  fun st g -> match g with
  | GenArg (g_ty, g_val) ->
    let st = hash_fold_abstract_argument_type st g_ty in
    hash_fold_generic g_ty st g_val

let hash_fold_generic_argument : type a. a Hash.folder -> a generic_argument Hash.folder =
  fun _level_tag g -> hash_fold_genarg_val g

let compare_genarg_val : type a. a generic_argument Ppx_compare_lib.compare =
  fun g1 g2 -> match g1 with
  | GenArg (g1_ty, g1_val) ->
    match g2 with
    | GenArg (g2_ty, g2_val) ->
      match Genarg.abstract_argument_type_eq g1_ty g2_ty with
      | Some Refl ->
        compare_generic g1_ty g1_val g2_val
      (* XXX: Technically, we should implement our own compare so ordering works *)
      | None -> 1

let compare_generic_argument : type a. a Ppx_compare_lib.compare -> a generic_argument Ppx_compare_lib.compare =
  fun _level_tag g -> compare_genarg_val g

let gen_abstype_of_sexp : Sexp.t -> rgen_argument = fun s ->
  match s with
  | List [Atom "GenArg"; List [ Atom "Rawwit"; sty]; sobj] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    RG (generic_des (Rawwit ty) sobj)
  | List [Atom "GenArg"; List [ Atom "Glbwit"; sty]; sobj] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    RG (generic_des (Glbwit ty) sobj)
  | List [Atom "GenArg"; List [ Atom "Topwit"; sty]; sobj] ->
    let (ArgumentType ty) = argument_type_of_sexp sty in
    RG (generic_des (Topwit ty) sobj)
  | _ -> raise (Failure "SEXP Exception in abstype")

let generic_argument_of_sexp _lvl sexp : 'a Genarg.generic_argument =
  let (RG ga) = gen_abstype_of_sexp sexp in
  Obj.magic ga

let rec yojson_to_sexp json = match json with
  | `String s -> Sexp.Atom s
  | `List s -> Sexp.List (List.map yojson_to_sexp s)
  | _ -> raise (Failure "ser_genarg: yojson_to_sexp")

let rec sexp_to_yojson sexp : Yojson.Safe.t =
  match sexp with
  | Sexp.Atom s -> `String s
  | List l -> `List (List.map sexp_to_yojson l)

let generic_argument_of_yojson lvl json =
  let sexp = yojson_to_sexp json in
  Result.Ok (generic_argument_of_sexp lvl sexp)

let generic_argument_to_yojson : type a. (a -> Yojson.Safe.t) -> a generic_argument -> Yojson.Safe.t =
  fun _level_tag g ->
  sexp_of_generic_argument (fun _ -> Atom "") g |> sexp_to_yojson

type 'a generic_argument = 'a Genarg.generic_argument

type glob_generic_argument =
  [%import: Genarg.glob_generic_argument]
  [@@deriving sexp,yojson,hash,compare]

type raw_generic_argument =
  [%import: Genarg.raw_generic_argument]
  [@@deriving sexp,yojson,hash,compare]

type typed_generic_argument =
  [%import: Genarg.typed_generic_argument]
  [@@deriving sexp,yojson,hash,compare]

let mk_uniform pin pout phash pcompare =
  { raw_ser = pin
  ; raw_des = pout
  ; raw_hash = phash
  ; raw_compare = pcompare

  ; glb_ser = pin
  ; glb_des = pout
  ; glb_hash = phash
  ; glb_compare = pcompare

  ; top_ser = pin
  ; top_des = pout
  ; top_hash = phash
  ; top_compare = pcompare
  }

module type GenSer0 = sig
  type t [@@deriving sexp,hash,compare]
end

module GS0 (M : GenSer0) = struct
  let genser = mk_uniform M.sexp_of_t M.t_of_sexp M.hash_fold_t M.compare
end

module type GenSer = sig
  type raw [@@deriving sexp,hash,compare]
  type glb [@@deriving sexp,hash,compare]
  type top [@@deriving sexp,hash,compare]
end

module GS (M : GenSer) = struct
  let genser =
    { raw_ser = M.sexp_of_raw
    ; raw_des = M.raw_of_sexp
    ; raw_hash = M.hash_fold_raw
    ; raw_compare = M.compare_raw

    ; glb_ser = M.sexp_of_glb
    ; glb_des = M.glb_of_sexp
    ; glb_hash = M.hash_fold_glb
    ; glb_compare = M.compare_glb

    ; top_ser = M.sexp_of_top
    ; top_des = M.top_of_sexp
    ; top_hash = M.hash_fold_top
    ; top_compare = M.compare_top
    }
end
