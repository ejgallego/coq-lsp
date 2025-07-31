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

module Names = Ser_names

module Extraction_plugin = struct
  module G_extraction = Extraction_plugin.G_extraction
  module Table = struct
    type int_or_id =
      [%import: Extraction_plugin.Table.int_or_id]
      [@@deriving sexp,yojson,hash,compare]
    type lang =
      [%import: Extraction_plugin.Table.lang]
      [@@deriving sexp,yojson,hash,compare]
  end
end

module WitII = struct
  type t = Extraction_plugin.Table.int_or_id
    [@@deriving sexp,yojson,hash,compare]
end

let ser_wit_int_or_id = let module M = Ser_genarg.GSV(WitII) in M.genser

module WitL = struct
  type t = Extraction_plugin.Table.lang
    [@@deriving sexp,yojson,hash,compare]
end

let ser_wit_language = let module M = Ser_genarg.GSV(WitL) in M.genser

module WitMN = struct
  type t = string
    [@@deriving sexp,yojson,hash,compare]
end

let ser_wit_mlname = let module M = Ser_genarg.GSV(WitMN) in M.genser

let register () =
  Ser_genarg.register_genser Extraction_plugin.G_extraction.wit_int_or_id ser_wit_int_or_id;
  Ser_genarg.register_genser Extraction_plugin.G_extraction.wit_language ser_wit_language;
  Ser_genarg.register_genser Extraction_plugin.G_extraction.wit_mlname ser_wit_mlname;
  ()

let _ = register ()
