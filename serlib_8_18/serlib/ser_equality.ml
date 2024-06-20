open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

type multi =
  [%import: Equality.multi]
  [@@deriving sexp,yojson,hash,compare]
