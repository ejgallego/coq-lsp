open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Libnames = Serlib.Ser_libnames
module Notation = Serlib.Ser_notation

type number_string_via =
  [%import: Number_string_notation_plugin.Number.number_string_via]
  [@@deriving sexp,yojson,hash,compare]

type number_option =
  [%import: Number_string_notation_plugin.Number.number_option]
  [@@deriving sexp,yojson,hash,compare]
