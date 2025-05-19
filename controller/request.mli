(************************************************************************)
(* Flèche => document manager: Document                                 *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1 / GPL3+      *)
(* Copyright 2025      CNRS                    -- LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

(* Request errors, we include execution feedback which could be very
   important *)
module Error : sig
  type 'a t =
    { code : int
    ; payload : 'a
    ; feedback : Lang.Range.t Coq.Message.t list
    }

  val make : ?feedback:Lang.Range.t Coq.Message.t list -> int -> 'a -> 'a t
end

module R : sig
  type ('r, 'e) t = ('r, 'e Error.t) Result.t

  val map_error : f:('e -> 'f) -> ('r, 'e) t -> ('r, 'f) t

  (* We don't allow to pass the feedback to the [f] handler yet, that's not
     hard, but I'd suggest waiting until the conversion of character points is
     working better. *)
  val of_execution :
       lines:string Array.t
    -> name:string
    -> f:('a -> (('r, string) t, Loc.t) Coq.Protect.E.t)
    -> 'a
    -> ('r, string) t
end

(* We could classify the requests that don't need to call-back Coq (and thus
   don't need the interruption token; but it is not worth it. *)
type ('r, 'e) document =
  token:Coq.Limits.Token.t -> doc:Fleche.Doc.t -> ('r, 'e) R.t

type ('r, 'e) position =
     token:Coq.Limits.Token.t
  -> doc:Fleche.Doc.t
  -> point:int * int
  -> ('r, 'e) R.t

(** Requests that require data access *)
module Data : sig
  type ('r, 'e) t =
    | Immediate of
        { uri : Lang.LUri.File.t
        ; handler : ('r, 'e) document
        }
    | DocRequest of
        { uri : Lang.LUri.File.t
        ; postpone : bool
        ; handler : ('r, 'e) document
        }
    | PosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        ; handler : ('r, 'e) position
        }

  (* Debug printing *)
  val data : Format.formatter -> ('r, 'e) t -> unit

  val dm_request :
    ('r, 'e) t -> Lang.LUri.File.t * bool * Fleche.Theory.Request.request

  val serve :
    token:Coq.Limits.Token.t -> doc:Fleche.Doc.t -> ('r, 'e) t -> ('r, 'e) R.t
end
