(************************************************************************)
(* Flèche Document Manager                                              *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2022 Inria           -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
type node =
  { ast : Lang.Ast.t  (** Ast of node *)
  ; state : Lang.State.t  (** (Full) State of node *)
  ; memo_info : string
  }

type t =
  { uri : string
  ; version : int
  ; contents : string
  ; root : Lang.State.t
  ; nodes : node list
  }

val create :
     state:Lang.State.t * Loadpath.vo_path list * string list * _
  -> uri:string
  -> version:int
  -> contents:string
  -> t

val check :
     ofmt:Format.formatter
  -> doc:t
  -> fb_queue:Lang.Message.t list ref
  -> t * Lang.State.t * Types.Diagnostic.t list
