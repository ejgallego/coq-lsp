(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Point : sig
  type t = Lang.Point.t [@@deriving yojson]
end

module Range : sig
  type t = Lang.Range.t [@@deriving yojson]
end

module LUri : sig
  module File : sig
    type t = Lang.LUri.File.t [@@deriving yojson]
  end
end

module Diagnostic : sig
  type t = Lang.Diagnostic.t [@@deriving to_yojson]
end

val mk_diagnostics :
  uri:Lang.LUri.File.t -> version:int -> Lang.Diagnostic.t list -> Yojson.Safe.t
