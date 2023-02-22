(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Lang = JLang

module TextDocumentItem = struct
  type t =
    { uri : Lang.LUri.File.t
    ; languageId : string
    ; version : int
    ; text : string
    }
  [@@deriving yojson]
end

module TextDocumentIdentifier = struct
  type t = { uri : Lang.LUri.File.t } [@@deriving yojson]
end

module VersionedTextDocumentIdentifier = struct
  type t =
    { uri : Lang.LUri.File.t
    ; version : int
    }
  [@@deriving yojson]
end
