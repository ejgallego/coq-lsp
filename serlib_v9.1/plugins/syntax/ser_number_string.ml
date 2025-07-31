(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Libnames = Serlib.Ser_libnames
module Notation = Serlib.Ser_notation

type number_string_via =
  [%import: Number_string_notation_plugin.Number_string.number_string_via]
  [@@deriving sexp,yojson,hash,compare]

type number_option =
  [%import: Number_string_notation_plugin.Number_string.number_option]
  [@@deriving sexp,yojson,hash,compare]
