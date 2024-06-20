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

module type SJHC = sig
  type t [@@deriving sexp,yojson,hash,compare]
end

module type SJHC1 = sig
  type 'a t [@@deriving sexp,yojson,hash,compare]
end

(* Bijection with serializable types *)
module type Bijectable = sig

  (* Base Type *)
  type t

  (* Representation type *)
  type _t [@@deriving sexp,yojson,hash,compare]

  (* Need to be bijetive *)
  val to_t : _t -> t
  val of_t : t -> _t

end

module Biject(M : Bijectable) : SJHC with type t = M.t = struct

  type t = M.t

  let sexp_of_t x = M.sexp_of__t (M.of_t x)
  let t_of_sexp s = M.to_t (M._t_of_sexp s)

  let to_yojson p = M._t_to_yojson (M.of_t p)
  let of_yojson p = M._t_of_yojson p |> Result.map M.to_t

  let hash x = M.hash__t (M.of_t x)
  let hash_fold_t st x = M.hash_fold__t st (M.of_t x)

  let compare x1 x2 = M.compare__t (M.of_t x1) (M.of_t x2)
end

(* Bijection with serializable types *)
module type Bijectable1 = sig

  (* Base Type *)
  type 'a t

  (* Representation type *)
  type 'a _t [@@deriving sexp,yojson,hash,compare]

  (* Need to be bijetive *)
  val to_t : 'a _t -> 'a t
  val of_t : 'a t -> 'a _t

end

module Biject1(M : Bijectable1) : SJHC1 with type 'a t = 'a M.t = struct

  type 'a t = 'a M.t

  let sexp_of_t f x = M.sexp_of__t f (M.of_t x)
  let t_of_sexp f s = M.to_t (M._t_of_sexp f s)

  let to_yojson f p = M._t_to_yojson f (M.of_t p)
  let of_yojson f p = M._t_of_yojson f p |> Result.map M.to_t

  let hash_fold_t f st x = M.hash_fold__t f st (M.of_t x)

  let compare f x1 x2 = M.compare__t f (M.of_t x1) (M.of_t x2)
end

(* We do our own alias as to have better control *)
let _sercast = Obj.magic

(* Obj.magic piercing *)
module type Pierceable = sig

  (* Type to pierce *)
  type t

  (* Representation type *)
  type _t [@@deriving sexp,yojson,hash,compare]
end

module type Pierceable1 = sig

  (* Type to pierce *)
  type 'a t

  (* Representation type *)
  type 'a _t [@@deriving sexp,yojson,hash,compare]
end

module Pierce(M : Pierceable) : SJHC with type t = M.t = struct

  type t = M.t

  let sexp_of_t x = M.sexp_of__t (_sercast x)
  let t_of_sexp s = _sercast (M._t_of_sexp s)

  let to_yojson p = M._t_to_yojson (_sercast p)
  let of_yojson p = M._t_of_yojson p |> Result.map _sercast

  let hash x = M.hash__t (_sercast x)
  let hash_fold_t st x = M.hash_fold__t st (_sercast x)

  let compare x1 x2 = M.compare__t (_sercast x1) (_sercast x2)

end

module Pierce1(M : Pierceable1) : SJHC1 with type 'a t = 'a M.t = struct

  type 'a t = 'a M.t

  let sexp_of_t f x = M.sexp_of__t f (_sercast x)
  let t_of_sexp f s = _sercast (M._t_of_sexp f s)

  let to_yojson f p = M._t_to_yojson f (_sercast p)
  let of_yojson f p = M._t_of_yojson f p |> Result.map _sercast

  (* let hash x = M.hash__t (_sercast x) *)
  let hash_fold_t f st x = M.hash_fold__t f st (_sercast x)

  let compare f x1 x2 = M.compare__t f (_sercast x1) (_sercast x2)

end

(* Unfortunately this doesn't really work for types that are named as
   the functions would have to be sexp_of_name etc... Maybe fixme in
   the future *)
module PierceAlt(M : Pierceable) : SJHC with type t := M.t = struct

  let sexp_of_t x = M.sexp_of__t (_sercast x)
  let t_of_sexp s = _sercast (M._t_of_sexp s)

  let to_yojson p = M._t_to_yojson (_sercast p)
  let of_yojson p = M._t_of_yojson p |> Result.map _sercast

  let hash x = M.hash__t (_sercast x)
  let hash_fold_t st x = M.hash_fold__t st (_sercast x)

  let compare x1 x2 = M.compare__t (_sercast x1) (_sercast x2)

end

module type OpaqueDesc = sig type t val name : string end

module Opaque(M : OpaqueDesc) : SJHC with type t = M.t = struct

  type t = M.t
  let typ = M.name

  let sexp_of_t x = Serlib_base.sexp_of_opaque ~typ x
  let t_of_sexp s = Serlib_base.opaque_of_sexp ~typ s

  let to_yojson p = Serlib_base.opaque_to_yojson ~typ p
  let of_yojson p = Serlib_base.opaque_of_yojson ~typ p

  let hash x = Serlib_base.hash_opaque ~typ x
  let hash_fold_t st x = Serlib_base.hash_fold_opaque ~typ st x

  let compare x1 x2 = Serlib_base.compare_opaque ~typ x1 x2

end

module type OpaqueDesc1 = sig type 'a t val name : string end

module Opaque1(M : OpaqueDesc1) : SJHC1 with type 'a t = 'a M.t = struct

  type 'a  t = 'a M.t
  let typ = M.name

  let sexp_of_t _ x = Serlib_base.sexp_of_opaque ~typ x
  let t_of_sexp _ s = Serlib_base.opaque_of_sexp ~typ s

  let to_yojson _ p = Serlib_base.opaque_to_yojson ~typ p
  let of_yojson _ p = Serlib_base.opaque_of_yojson ~typ p

  let hash_fold_t _ st x = Serlib_base.hash_fold_opaque ~typ st x

  let compare _ x1 x2 = Serlib_base.compare_opaque ~typ x1 x2

end
