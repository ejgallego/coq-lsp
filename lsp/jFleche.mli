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
  -> Yojson.Safe.t

(** Goals *)
module Message : sig
  type 'a t =
    { range : JLang.Range.t option
    ; level : int
    ; text : 'a
    }
end

module GoalsAnswer : sig
  type 'pp t =
    { textDocument : Doc.VersionedTextDocumentIdentifier.t
    ; position : Lang.Point.t
    ; goals : 'pp Coq.Goals.reified_pp option [@default None]
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
  type t =
    { range : Lang.Range.t
    ; span : Coq.Ast.t option [@default None]
    }
  [@@deriving to_yojson]
end

module FlecheDocument : sig
  type t =
    { spans : RangedSpan.t list
    ; completed : CompletionStatus.t
    }
  [@@deriving to_yojson]
end
