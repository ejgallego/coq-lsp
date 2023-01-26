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

    module Extra = struct
      type t = [%import: Fleche.Types.Diagnostic.Extra.t] [@@deriving yojson]
    end

    type t = [%import: Fleche.Types.Diagnostic.t] [@@deriving yojson]
  end
end

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

let mk_progress ~uri ~version processing =
  let textDocument = { Base.VersionedTextDocument.uri; version } in
  let params = Progress.to_yojson { Progress.textDocument; processing } in
  Base.mk_notification ~method_:"$/coq/fileProgress" ~params
