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

let cmake = CAst.make

module Loc   = Ser_loc
module CAst  = Ser_cAst
module Names = Ser_names

type _t =
  | Ser_Qualid of Names.DirPath.t * Names.Id.t
    [@@deriving sexp,yojson,hash,compare]

let _t_put qid =
  let (dp, id) = Libnames.repr_qualid (cmake qid) in
  Ser_Qualid (dp, id)

let _t_get (Ser_Qualid (dp, id)) = Libnames.(make_qualid dp id).CAst.v

type qualid_r =
  [%import: Libnames.qualid_r]

let qualid_r_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_qualid_r qid  = sexp_of__t (_t_put qid)

let qualid_r_of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let qualid_r_to_yojson level = _t_to_yojson (_t_put level)

(* let hash_qualid_r x = hash__t (_t_put x) *)
let hash_fold_qualid_r st x = hash_fold__t st (_t_put x)
let compare_qualid_r x y = compare__t (_t_put x) (_t_put y)

(* qualid: private *)
type qualid =
  [%import: Libnames.qualid]
  [@@deriving sexp,yojson,hash,compare]

module FP = struct
  type _t =
    { dirpath : Names.DirPath.t
    ; basename : Names.Id.t }
  [@@deriving sexp,yojson,hash,compare]

  let _t_get { dirpath; basename } = Libnames.make_path dirpath basename
  let _t_put fp = let dirpath, basename = Libnames.repr_path fp in { dirpath; basename }
end

open FP

type full_path = Libnames.full_path
let full_path_of_sexp sexp = _t_get (_t_of_sexp sexp)
let sexp_of_full_path qid  = sexp_of__t (_t_put qid)

let full_path_of_yojson json = Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _t_get)
let full_path_to_yojson level = _t_to_yojson (_t_put level)

let hash_full_path x = hash__t (_t_put x)
let hash_fold_full_path st x = hash_fold__t st (_t_put x)

let compare_full_path x y = compare__t (_t_put x) (_t_put y)
