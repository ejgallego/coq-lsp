open Serlib

open Sexplib.Conv
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module Libnames = Ser_libnames
module Notation = Ser_notation

module A1 = struct
  type raw = Notation.numnot_option
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_deprecated_number_modifier = let module M = Ser_genarg.GS(A1) in M.genser

module A2 = struct
  type raw = Ser_number.number_option
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_modifier = let module M = Ser_genarg.GS(A2) in M.genser

module A3 = struct
  type raw = Ser_number.number_option list
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_options = let module M = Ser_genarg.GS(A3) in M.genser

module A4 = struct
  type raw = bool * Libnames.qualid * Libnames.qualid
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_string_mapping = let module M = Ser_genarg.GS(A4) in M.genser

module A5 = struct
  type raw = Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_string_via = let module M = Ser_genarg.GS(A5) in M.genser

module A6 = struct
  type raw = Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_string_option = let module M = Ser_genarg.GS(A6) in M.genser

let register () =
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_deprecated_number_modifier ser_wit_deprecated_number_modifier;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_modifier ser_wit_number_modifier;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_options ser_wit_number_options;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_string_mapping ser_wit_number_string_mapping;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_string_via ser_wit_number_string_via;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_string_option ser_wit_string_option;
  ()

let _ = register ()
