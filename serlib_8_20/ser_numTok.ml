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

type sign =
  [%import: NumTok.sign]
  [@@deriving sexp,yojson,hash,compare]

type num_class =
  [%import: NumTok.num_class]
  [@@deriving sexp,yojson]

type 'a exp =
  [%import: 'a NumTok.exp]
  [@@deriving sexp,yojson]

module Unsigned = struct

  module PierceSpec = struct
    type t = NumTok.Unsigned.t
    type _t = {
      int : string;
      frac : string;
      exp : string
    } [@@deriving sexp,yojson,hash,compare]
  end

  include SerType.Pierce(PierceSpec)
end

module UnsignedNat = struct
  module USNBij = struct
    type t = NumTok.UnsignedNat.t
    type _t = string [@@deriving sexp,yojson,hash,compare]
    let to_t = NumTok.UnsignedNat.of_string
    let of_t = NumTok.UnsignedNat.to_string
  end
  include SerType.Biject(USNBij)
end

module Signed = struct

  type t =
    [%import: NumTok.Signed.t]
    [@@deriving sexp,yojson,hash,compare]

end
