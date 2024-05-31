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

(* Example of serialization to a sexp:

   Coq's main datatype, constr, is a private type so we need to define
   a serializable clone. Unfortunately, its main view is "zippy" so we
   need to recurse throu the constr to build the clone.
*)

open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

let hash_fold_array = hash_fold_array_frozen

module SList   = Ser_sList
module Names   = Ser_names
module Sorts   = Ser_sorts
module Evar    = Ser_evar
module Univ    = Ser_univ
module UVars   = Ser_uvars
module Context = Ser_context
module Uint63  = Ser_uint63
module Float64 = Ser_float64

type metavariable =
  [%import: Constr.metavariable]
  [@@deriving sexp, yojson, hash, compare]

type pconstant =
  [%import: Constr.pconstant]
  [@@deriving sexp, yojson, hash, compare]

type pinductive =
  [%import: Constr.pinductive]
  [@@deriving sexp, yojson, hash, compare]

type pconstructor =
  [%import: Constr.pconstructor]
  [@@deriving sexp, yojson, hash, compare]

type cast_kind =
  [%import: Constr.cast_kind]
  [@@deriving sexp,yojson,hash,compare]

type case_style =
  [%import: Constr.case_style]
  [@@deriving sexp,yojson,hash,compare]

type case_printing =
  [%import: Constr.case_printing]
  [@@deriving sexp,yojson,hash,compare]

type case_info =
  [%import: Constr.case_info]
  [@@deriving sexp,yojson, hash, compare]

type 'constr pexistential =
  [%import: 'constr Constr.pexistential]
  [@@deriving sexp,yojson,hash,compare]

type ('constr, 'types, 'r) prec_declaration =
  [%import: ('constr, 'types, 'r) Constr.prec_declaration]
  [@@deriving sexp,yojson,hash,compare]

type ('constr, 'types, 'r) pfixpoint =
  [%import: ('constr, 'types, 'r) Constr.pfixpoint]
  [@@deriving sexp,yojson,hash,compare]

type ('constr, 'types, 'r) pcofixpoint =
  [%import: ('constr, 'types, 'r) Constr.pcofixpoint]
  [@@deriving sexp,yojson,hash,compare]

type 'constr pcase_invert =
  [%import: 'constr Constr.pcase_invert]
  [@@deriving sexp,yojson,hash,compare]

let map_pcase_invert f = function
  | NoInvert -> NoInvert
  | CaseInvert { indices } ->
    CaseInvert { indices = Array.map f indices }

type ('constr, 'r) pcase_branch =
  [%import: ('constr, 'r) Constr.pcase_branch]
  [@@deriving sexp,yojson,hash,compare]

let map_pcase_branch f (bi, c) = (bi, f c)

type ('types, 'r) pcase_return =
  [%import: ('types, 'r) Constr.pcase_return]
  [@@deriving sexp,yojson,hash,compare]

let map_pcase_return f (bi, c) = (bi, f c)

type _constr =
  | Rel       of int
  | Var       of Names.Id.t
  | Meta      of int
  | Evar      of _constr pexistential
  | Sort      of Sorts.t
  | Cast      of _constr * cast_kind * _constr
  | Prod      of (Names.Name.t, Sorts.relevance) Context.pbinder_annot * _constr * _constr
  | Lambda    of (Names.Name.t, Sorts.relevance) Context.pbinder_annot * _constr * _constr
  | LetIn     of (Names.Name.t, Sorts.relevance) Context.pbinder_annot * _constr * _constr * _constr
  | App       of _constr * _constr array
  | Const     of pconstant
  | Ind       of pinductive
  | Construct of pconstructor
  | Case      of case_info * UVars.Instance.t * _constr array * (_constr, Sorts.relevance) pcase_return * _constr pcase_invert *  _constr * (_constr, Sorts.relevance) pcase_branch array
  | Fix       of (_constr, _constr, Sorts.relevance) pfixpoint
  | CoFix     of (_constr, _constr, Sorts.relevance) pcofixpoint
  | Proj      of Names.Projection.t * Sorts.relevance * _constr
  | Int       of Uint63.t
  | Float     of Float64.t
  | Array     of UVars.Instance.t * _constr array * _constr * _constr
[@@deriving sexp,yojson,hash,compare]

let rec _constr_put (c : Constr.t) : _constr =
  let cr  = _constr_put           in
  let crl = SList.map _constr_put in
  let cra = Array.map _constr_put in
  let crci = map_pcase_invert _constr_put in
  let crcb = map_pcase_branch _constr_put in
  let crcr = map_pcase_return _constr_put in
  let module C = Constr           in
  match C.kind c with
  | C.Rel i               -> Rel(i)
  | C.Var v               -> Var(v)
  | C.Meta(mv)            -> Meta mv
  | C.Evar(ek, csa)       -> Evar (ek, crl csa)
  | C.Sort(st)            -> Sort (st)
  | C.Cast(cs,k,ty)       -> Cast(cr cs, k, cr ty)
  | C.Prod(n,tya,tyr)     -> Prod(n, cr tya, cr tyr)
  | C.Lambda(n,ab,bd)     -> Lambda(n, cr ab, cr bd)
  | C.LetIn(n,u,ab,bd)    -> LetIn(n, cr u, cr ab, cr bd)
  | C.App(hd, al)         -> App(cr hd, cra al)
  | C.Const p             -> Const p
  | C.Ind(p,q)            -> Ind (p,q)
  | C.Construct(p)        -> Construct (p)
  | C.Case(ci, u, ca, (pr,r), pi, c, pb) ->
    Case(ci, u, cra ca, (crcr pr,r), crci pi, cr c, Array.map crcb pb)
  (* (int array * int) * (Name.t array * 'types array * 'constr array)) *)
  | C.Fix(p,(na,u1,u2))   -> Fix(p, (na, cra u1, cra u2))
  | C.CoFix(p,(na,u1,u2)) -> CoFix(p, (na, cra u1, cra u2))
  | C.Proj(p,r,c)           -> Proj(p, r, cr c)
  | C.Int i               -> Int i
  | C.Float i             -> Float i
  | C.Array (u,a,e,t)     -> Array(u, cra a, cr e, cr t)

let rec _constr_get (c : _constr) : Constr.t =
  let cr  = _constr_get           in
  let crl = SList.map _constr_get in
  let cra = Array.map _constr_get in
  let crci = map_pcase_invert _constr_get in
  let crcb = map_pcase_branch _constr_get in
  let crcr = map_pcase_return _constr_get in
  let module C = Constr           in
  match c with
  | Rel i               -> C.mkRel i
  | Var v               -> C.mkVar v
  | Meta(mv)            -> C.mkMeta mv
  | Evar(ek, csa)       -> C.mkEvar (ek, crl csa)
  | Sort(st)            -> C.mkSort (st)
  | Cast(cs,k,ty)       -> C.mkCast(cr cs, k, cr ty)
  | Prod(n,tya,tyr)     -> C.mkProd(n, cr tya, cr tyr)
  | Lambda(n,ab,bd)     -> C.mkLambda(n, cr ab, cr bd)
  | LetIn(n,u,ab,bd)    -> C.mkLetIn(n, cr u, cr ab, cr bd)
  | App(hd, al)         -> C.mkApp(cr hd, cra al)
  | Const p             -> C.mkConstU(p)
  | Ind(p,q)            -> C.mkIndU(p, q)
  | Construct(p)        -> C.mkConstructU(p)
  | Case(ci, u, ca, (pr,r), pi, c, pb) -> C.mkCase (ci, u, cra ca, (crcr pr,r), crci pi, cr c, Array.map crcb pb)
  | Fix (p,(na,u1,u2))  -> C.mkFix(p, (na, cra u1, cra u2))
  | CoFix(p,(na,u1,u2)) -> C.mkCoFix(p, (na, cra u1, cra u2))
  | Proj(p,r,c)           -> C.mkProj(p, r, cr c)
  | Int i               -> C.mkInt i
  | Float f             -> C.mkFloat f
  | Array (u,a,e,t)     -> C.mkArray(u, cra a, cr e, cr t)

module ConstrBij = struct

  type t = Constr.t

  type _t = _constr
  [@@deriving sexp,yojson,hash,compare]

  let to_t = _constr_get
  let of_t = _constr_put

end

module CC = SerType.Biject(ConstrBij)
type constr = CC.t
 [@@deriving sexp,yojson,hash,compare]
type types = CC.t
 [@@deriving sexp,yojson,hash,compare]

type t = constr
 [@@deriving sexp,yojson,hash,compare]

type case_invert =
  [%import: Constr.case_invert]
  [@@deriving sexp,yojson]

type rec_declaration =
  [%import: Constr.rec_declaration]
  [@@deriving sexp]

type fixpoint =
  [%import: Constr.fixpoint]
  [@@deriving sexp]

type cofixpoint =
  [%import: Constr.cofixpoint]
  [@@deriving sexp]

type existential =
  [%import: Constr.existential]
  [@@deriving sexp]

type sorts_family = Sorts.family
let sorts_family_of_sexp = Sorts.family_of_sexp
let sexp_of_sorts_family = Sorts.sexp_of_family

type named_declaration =
  [%import: Constr.named_declaration]
  [@@deriving sexp,yojson,hash,compare]

type named_context =
  [%import: Constr.named_context]
  [@@deriving sexp,yojson,hash,compare]

type rel_declaration =
  [%import: Constr.rel_declaration]
  [@@deriving sexp,yojson,hash,compare]

type rel_context =
  [%import: Constr.rel_context]
  [@@deriving sexp,yojson,hash,compare]
