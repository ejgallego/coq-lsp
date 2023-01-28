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

module Config = struct
  type t = [%import: Fleche.Config.t] [@@deriving yojson]
end

module Types = struct
  module Point = struct
    type t = [%import: Fleche.Types.Point.t] [@@deriving yojson]
  end

  module Range = struct
    type t = [%import: Fleche.Types.Range.t] [@@deriving yojson]
  end

  module Diagnostic = struct
    module Libnames = Serlib.Ser_libnames

    (* Current Flèche diagnostic is not LSP-standard compliant, this one is *)
    type t =
      { range : Range.t
      ; severity : int
      ; message : string
      }
    [@@deriving yojson]

    let to_yojson
        { Fleche.Types.Diagnostic.range; severity; message; extra = _ } =
      let message = Pp.to_string message in
      to_yojson { range; severity; message }
  end
end

let mk_diagnostics ~uri ~version ld : Yojson.Safe.t =
  let diags = List.map Types.Diagnostic.to_yojson ld in
  let params =
    `Assoc
      [ ("uri", `String uri)
      ; ("version", `Int version)
      ; ("diagnostics", `List diags)
      ]
  in
  Base.mk_notification ~method_:"textDocument/publishDiagnostics" ~params

module Progress = struct
  module Info = struct
    type t =
      [%import:
        (Fleche.Progress.Info.t[@with Fleche.Types.Range.t := Types.Range.t])]
    [@@deriving yojson]
  end

  type t =
    { textDocument : Base.VersionedTextDocument.t
    ; processing : Info.t list
    }
  [@@deriving yojson]
end

let mk_progress ~uri ~version processing =
  let textDocument = { Base.VersionedTextDocument.uri; version } in
  let params = Progress.to_yojson { Progress.textDocument; processing } in
  Base.mk_notification ~method_:"$/coq/fileProgress" ~params

module GoalsAnswer = struct
  type t =
    { textDocument : Base.VersionedTextDocument.t
    ; position : Types.Point.t
    ; goals : string JCoq.Goals.reified_goal JCoq.Goals.goals option
    ; messages : string list
    ; error : string option
    }
  [@@deriving yojson]
end

let mk_goals ~uri ~version ~position ~goals ~messages ~error =
  let f rg = Coq.Goals.map_reified_goal ~f:Pp.to_string rg in
  let goals = Option.map (Coq.Goals.map_goals ~f) goals in
  let messages = List.map Pp.to_string messages in
  let error = Option.map Pp.to_string error in
  GoalsAnswer.to_yojson
    { textDocument = { uri; version }; position; goals; messages; error }

module Location = struct
  type t =
    { uri : string
    ; range : Types.Range.t
    }
  [@@deriving yojson]
end

module SymInfo = struct
  type t =
    { name : string
    ; kind : int
    ; location : Location.t
    }
  [@@deriving yojson]
end

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
    ; range : Types.Range.t option
    }
  [@@deriving yojson]
end
