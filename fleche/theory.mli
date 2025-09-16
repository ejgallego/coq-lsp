(************************************************************************)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)
(* Flèche => document manager: theories                                 *)
(************************************************************************)

module Check : sig
  (** Check pending documents, return [None] if there is none pending, or
      [Some rqs] the list of requests ready to execute after the check. Sends
      progress and diagnostics notifications using output function [ofn]. *)
  val maybe_check :
    io:Io.CallBack.t -> token:Coq.Limits.Token.t -> (Int.Set.t * Doc.t) option

  val set_scheduler_hint : uri:Lang.LUri.File.t -> point:int * int -> unit
end

(** Open a document inside a theory *)
val open_ :
     io:Io.CallBack.t
  -> token:Coq.Limits.Token.t
  -> env:Doc.Env.t
  -> uri:Lang.LUri.File.t
  -> languageId:string
  -> raw:string
  -> version:int
  -> unit

(** Update a document inside a theory, returns the list of not valid requests *)
val change :
     io:Io.CallBack.t
  -> token:Coq.Limits.Token.t
  -> uri:Lang.LUri.File.t
  -> version:int
  -> raw:string
  -> Int.Set.t

(** Close a document *)
val close : uri:Lang.LUri.File.t -> unit

module Request : sig
  type request =
    | Immediate
    | FullDoc
    | PosInDoc of
        { point : int * int
        ; version : int option
        }

  type t =
    { id : int
    ; uri : Lang.LUri.File.t
    ; postpone : bool
    ; request : request
    }

  type action =
    | Now of Doc.t
    | Postpone
    | Cancel

  (** Add a request to be served; returns [Postpone] if request is added to the
      queue, [Now doc] if the request is available. [Cancel] means "we will
      never be able to serve this" *)
  val add : t -> action

  (** Removes the request from the list of things to wake up *)
  val remove : t -> unit
end

(* Experimental plugin API, not stable yet *)
module Register : sig
  (** List of additional includes to inject into a document *)
  module InjectRequire : sig
    type t = io:Io.CallBack.t -> Coq.Workspace.Require.t list

    val add : t -> unit
  end

  (** Run an action when a document has completed checking, attention, with or
      without errors. *)
  module Completed : sig
    type t = io:Io.CallBack.t -> token:Coq.Limits.Token.t -> doc:Doc.t -> unit

    val add : t -> unit
  end
end
