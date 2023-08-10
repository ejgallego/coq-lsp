(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Lang = JLang

module DidChangeConfigurationParams = struct
  type t =
    { settings : Yojson.Safe.t
    }
  [@@deriving yojson]
end

module WorkspaceFolder = struct
  type t =
    { uri : Lang.LUri.File.t
    ; name : string
    }
  [@@deriving yojson]
end

module WorkspaceFoldersChangeEvent = struct
  type t =
    { added : WorkspaceFolder.t list
    ; removed : WorkspaceFolder.t list
    }
  [@@deriving yojson]
end

module DidChangeWorkspaceFoldersParams = struct
  type t = { event : WorkspaceFoldersChangeEvent.t } [@@deriving yojson]
end
