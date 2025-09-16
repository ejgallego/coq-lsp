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

(** This module contains the OCaml specification of Flèche's / coq-lsp
    extensions to LSP *)

(** Server config *)
module Config : sig
  type t = Fleche.Config.t [@@deriving yojson]
end

(** FileProgress support *)
val mk_progress :
     uri:Lang.LUri.File.t
  -> version:int
  -> Fleche.Progress.Info.t list
  -> Base.Notification.t

module FileProgress : sig
  type t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; processing : Fleche.Progress.Info.t list
    }
  [@@deriving yojson]
end

(** Goals *)
module Message : sig
  type 'a t =
    { range : JLang.Range.t option
    ; level : int
    ; text : 'a
    }
  [@@deriving yojson]

  val of_coq_message : Lang.Range.t Coq.Message.t -> Pp.t t
  val map : f:('a -> 'b) -> 'a t -> 'b t
end

module GoalsAnswer : sig
  type ('goals, 'pp) t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; position : Lang.Point.t
    ; range : Lang.Range.t option [@default None]
    ; goals : ('goals, 'pp) JCoq.Goals.reified option [@default None]
    ; program : JCoq.Declare.OblState.View.t Names.Id.Map.t option
          [@default None]
    ; messages : 'pp Message.t list
    ; error : 'pp option [@default None]
    }
  [@@deriving to_yojson]
end

(** Coq-lsp-specific *)
module CompletionStatus : sig
  type t =
    { status : [ `Yes | `Stopped | `Failed ]
    ; range : Lang.Range.t
    }
  [@@deriving yojson]
end

module RangedSpan : sig
  type ('goals, 'pp) t =
    { range : Lang.Range.t
    ; ast : Coq.Ast.t option [@default None]
    ; goals : ('goals, 'pp) GoalsAnswer.t option [@default None]
    }
  [@@deriving yojson]
end

module FlecheDocument : sig
  type ('goals, 'pp) t =
    { spans : ('goals, 'pp) RangedSpan.t list
    ; completed : CompletionStatus.t
    }
  [@@deriving to_yojson]
end

module SentencePerfData : sig
  type t = Fleche.Perf.Sentence.t [@@deriving yojson]
end

module DocumentPerfData : sig
  type t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; summary : string
    ; timings : SentencePerfData.t list
    }
  [@@deriving yojson]
end

val mk_perf :
  uri:Lang.LUri.File.t -> version:int -> Fleche.Perf.t -> Base.Notification.t

(* Server status notifications *)
val mk_serverVersion : Fleche.ServerInfo.Version.t -> Base.Notification.t
val mk_serverStatus : Fleche.ServerInfo.Status.t -> Base.Notification.t

(** Exec Info *)
val mk_execinfo :
     uri:Lang.LUri.File.t
  -> version:int
  -> range:Lang.Range.t
  -> Base.Notification.t
