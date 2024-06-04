(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Serlib

open Sexplib.Conv
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module Libnames = Ser_libnames
module Notation = Ser_notation

module A2 = struct
  type t = Ser_number_string.number_option
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_modifier = let module M = Ser_genarg.GSV(A2) in M.genser

module A3 = struct
  type t = Ser_number_string.number_option list
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_options = let module M = Ser_genarg.GSV(A3) in M.genser

module A4 = struct
  type t = bool * Libnames.qualid * Libnames.qualid
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_string_mapping = let module M = Ser_genarg.GSV(A4) in M.genser

module A5 = struct
  type t = Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list
  [@@deriving sexp,hash,compare]
end

let ser_wit_number_string_via = let module M = Ser_genarg.GSV(A5) in M.genser

module A6 = struct
  type t = Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list
  [@@deriving sexp,hash,compare]
end

let ser_wit_string_option = let module M = Ser_genarg.GSV(A6) in M.genser

let register () =
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_modifier ser_wit_number_modifier;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_options ser_wit_number_options;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_string_mapping ser_wit_number_string_mapping;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_number_string_via ser_wit_number_string_via;
  Ser_genarg.register_genser Number_string_notation_plugin.G_number_string.wit_string_option ser_wit_string_option;
  ()

let _ = register ()
