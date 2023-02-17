(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module WorkspaceFolder : sig
  type t =
    { uri : Lang.LUri.File.t
    ; name : string
    }
  [@@deriving yojson]
end

module WorkspaceFoldersChangeEvent : sig
  type t =
    { added : WorkspaceFolder.t list
    ; removed : WorkspaceFolder.t list
    }
  [@@deriving yojson]
end

module DidChangeWorkspaceFoldersParams : sig
  type t = { event : WorkspaceFoldersChangeEvent.t } [@@deriving yojson]
end
