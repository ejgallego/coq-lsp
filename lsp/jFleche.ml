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
module Ast = JCoq.Ast
module Lang = JLang
module Names = Serlib.Ser_names

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

module FileProgress = struct
  module Info = struct
    type t = [%import: Fleche.Progress.Info.t] [@@deriving yojson]
  end

  type t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; processing : Info.t list
    }
  [@@deriving yojson]
end

let mk_progress ~uri ~version processing =
  let textDocument = { Doc.VersionedTextDocumentIdentifier.uri; version } in
  let params =
    FileProgress.to_yojson { FileProgress.textDocument; processing }
    |> Yojson.Safe.Util.to_assoc
  in
  Base.Notification.make ~method_:"$/coq/fileProgress" ~params ()

module Message = struct
  type 'a t =
    { range : JLang.Range.t option
    ; level : int
    ; text : 'a
    }
  [@@deriving yojson]

  let _map ~f { range; level; text } =
    let text = f text in
    { range; level; text }
end

module GoalsAnswer = struct
  type 'pp t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; position : Lang.Point.t
    ; goals : 'pp JCoq.Goals.reified_pp option [@default None]
    ; program : JCoq.Declare.OblState.View.t Names.Id.Map.t option
          [@default None]
    ; messages : 'pp Message.t list
    ; error : 'pp option [@default None]
    }
  [@@deriving to_yojson]
end

(** Pull Diagnostics *)
module CompletionStatus = struct
  type t =
    { status : [ `Yes | `Stopped | `Waiting of string list | `Failed ]
    ; range : Lang.Range.t
    }
  [@@deriving yojson]
end

module RangedSpan = struct
  type t =
    { range : Lang.Range.t
    ; span : Ast.t option [@default None]
    }
  [@@deriving yojson]
end

module FlecheDocument = struct
  type t =
    { spans : RangedSpan.t list
    ; completed : CompletionStatus.t
    }
  [@@deriving yojson]
end

module Info = struct
  type t = [%import: Fleche.Perf.Info.t] [@@deriving yojson]
end

module SentencePerfData = struct
  type t = [%import: Fleche.Perf.Sentence.t] [@@deriving yojson]
end

module DocumentPerfData = struct
  type t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; summary : string
    ; timings : SentencePerfData.t list
    }
  [@@deriving yojson]
end

let mk_perf ~uri ~version perf =
  let textDocument = { Doc.VersionedTextDocumentIdentifier.uri; version } in
  let params =
    let { Fleche.Perf.summary; timings } = perf in
    DocumentPerfData.(
      to_yojson { textDocument; summary; timings } |> Yojson.Safe.Util.to_assoc)
  in
  Base.Notification.make ~method_:"$/coq/filePerfData" ~params ()

module ServerVersion = struct
  type t = [%import: Fleche.ServerInfo.Version.t] [@@deriving yojson]
end

let mk_serverVersion vi =
  let params = ServerVersion.to_yojson vi |> Yojson.Safe.Util.to_assoc in
  Base.Notification.make ~method_:"$/coq/serverVersion" ~params ()

let mk_serverStatus (st : Fleche.ServerInfo.Status.t) =
  let params =
    match st with
    | Stopped -> [ ("status", `String "Stopped") ]
    | Idle mem -> [ ("status", `String "Idle"); ("mem", `String mem) ]
    | Running modname ->
      [ ("status", `String "Busy"); ("modname", `String modname) ]
  in
  Base.Notification.make ~method_:"$/coq/serverStatus" ~params ()
