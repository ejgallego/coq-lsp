(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Copyright 2019-2022 Inria                                            *)
(************************************************************************)

module type SJHC = sig

  type t [@@deriving sexp,yojson,hash,compare]

end

module type SJHC1 = sig

  type 'a t [@@deriving sexp,yojson,hash,compare]

end

(** Bijection with serializable types *)
module type Bijectable = sig

  (* Base Type *)
  type t

  (* Representation type *)
  type _t [@@deriving sexp,yojson,hash,compare]

  (* Need to be bijetive *)
  val to_t : _t -> t
  val of_t : t -> _t

end

module Biject(M : Bijectable) : SJHC with type t = M.t

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

module Biject1(M : Bijectable1) : SJHC1 with type 'a t = 'a M.t

module type Pierceable = sig

  (** Type to pierce *)
  type t

  (** Representation type *)
  type _t [@@deriving sexp,yojson,hash,compare]

end

module type Pierceable1 = sig

  (** Type to pierce *)
  type 'a t

  (** Representation type *)
  type 'a _t [@@deriving sexp,yojson,hash,compare]
end

module Pierce(M : Pierceable) : SJHC with type t = M.t
module Pierce1(M : Pierceable1) : SJHC1 with type 'a t = 'a M.t

module type OpaqueDesc = sig type t val name : string end
module Opaque(M : OpaqueDesc) : SJHC with type t = M.t

module type OpaqueDesc1 = sig type 'a t val name : string end
module Opaque1(M : OpaqueDesc1) : SJHC1 with type 'a t = 'a M.t
