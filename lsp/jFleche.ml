(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Pp = JCoq.Pp
module Lang = JLang

module Config = struct
  module Unicode_completion = struct
    type t = [%import: Fleche.Config.Unicode_completion.t]

    let to_yojson = function
      | Off -> `String "off"
      | Internal_small -> `String "internal"
      | Normal -> `String "normal"
      | Extended -> `String "extended"

    let of_yojson (j : Yojson.Safe.t) : (t, string) Result.t =
      match j with
      | `String "off" -> Ok Off
      | `String "internal" -> Ok Internal_small
      | `String "normal" -> Ok Normal
      | `String "extended" -> Ok Extended
      | _ ->
        Error
          "Fleche.Config.Unicode_completion.t: expected one of \
           [off,normal,extended]"
  end

  type t = [%import: Fleche.Config.t] [@@deriving yojson]
end

module Progress = struct
  module Info = struct
    type t = [%import: Fleche.Progress.Info.t] [@@deriving yojson]
  end

  type t =
    { textDocument : Doc.VersionedTextDocument.t
    ; processing : Info.t list
    }
  [@@deriving yojson]
end

let mk_progress ~uri ~version processing =
  let textDocument = { Doc.VersionedTextDocument.uri; version } in
  let params = Progress.to_yojson { Progress.textDocument; processing } in
  Base.mk_notification ~method_:"$/coq/fileProgress" ~params

module Message = struct
  type 'a t =
    { range : JLang.Range.t option
    ; level : int
    ; text : 'a
    }
  [@@deriving yojson]

  let map ~f { range; level; text } =
    let text = f text in
    { range; level; text }
end

module GoalsAnswer = struct
  type t =
    { textDocument : Doc.VersionedTextDocument.t
    ; position : Lang.Point.t
    ; goals : string JCoq.Goals.reified_goal JCoq.Goals.goals option
    ; messages : string Message.t list
    ; error : string option [@default None]
    }
  [@@deriving to_yojson]
end

let mk_goals ~uri ~version ~position ~goals ~messages ~error =
  let f rg = Coq.Goals.map_reified_goal ~f:Pp.to_string rg in
  let goals = Option.map (Coq.Goals.map_goals ~f) goals in
  let messages = List.map (Message.map ~f:Pp.to_string) messages in
  let error = Option.map Pp.to_string error in
  GoalsAnswer.to_yojson
    { textDocument = { uri; version }; position; goals; messages; error }

(** {1 document/definition} *)
module LocationLink = struct
  type t =
    { originSelectionRange : Lang.Range.t option [@default None]
    ; targetUri : Lang.LUri.File.t
    ; targetRange : Lang.Range.t
    ; targetSelectionRange : Lang.Range.t
    }
  [@@deriving yojson]
end
(** {1} DocumentSymbols *)

module DocumentSymbol = struct
  type t =
    { name : string
    ; detail : string option [@default None]
    ; kind : int
    ; tags : int list option [@default None]
    ; deprecated : bool option [@default None]
    ; range : Lang.Range.t
    ; selectionRange : Lang.Range.t
    ; children : t list option [@default None]
    }
  [@@deriving yojson]
end

(** Not used as of today, superseded by DocumentSymbol *)
module Location = struct
  type t =
    { uri : Lang.LUri.File.t
    ; range : Lang.Range.t
    }
  [@@deriving yojson]
end

(** Not used as of today, superseded by DocumentSymbol *)
module SymInfo = struct
  type t =
    { name : string
    ; kind : int
    ; location : Location.t
    }
  [@@deriving yojson]
end

(** {1} Hover *)

module HoverContents = struct
  type t =
    { kind : string
    ; value : string
    }
  [@@deriving yojson]
end

module HoverInfo = struct
  type t =
    { contents : HoverContents.t
    ; range : Lang.Range.t option [@default None]
    }
  [@@deriving yojson]
end

(** {1} Completion *)

module LabelDetails = struct
  type t = { detail : string } [@@deriving yojson]
end

module TextEditReplace = struct
  type t =
    { insert : Lang.Range.t
    ; replace : Lang.Range.t
    ; newText : string
    }
  [@@deriving yojson]
end

module CompletionData = struct
  type t =
    { label : string
    ; insertText : string option [@default None]
    ; labelDetails : LabelDetails.t option [@default None]
    ; textEdit : TextEditReplace.t option [@default None]
    ; commitCharacters : string list option [@default None]
    }
  [@@deriving yojson]
end
