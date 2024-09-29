(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Lang_ = Lang
module Lang = JLang

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

module TextEdit = struct
  type t =
    { range : Lang.Range.t
    ; newText : string
    }
  [@@deriving yojson]
end

module WorkspaceEdit = struct
  type t = { changes : (Lang.LUri.File.t * TextEdit.t list) list }
  [@@deriving of_yojson]

  let tok (uri, edits) =
    ( Lang_.LUri.File.to_string_uri uri
    , `List (List.map TextEdit.to_yojson edits) )

  let to_yojson { changes } =
    `Assoc [ ("changes", `Assoc (List.map tok changes)) ]
end
