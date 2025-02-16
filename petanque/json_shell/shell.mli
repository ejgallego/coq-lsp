open Petanque

(** I/O handling, by default, print to stderr *)

(** [trace header extra message] *)
val trace_ref : (string -> ?verbose:string -> string -> unit) ref

(** [message level message] *)
val message_ref : (lvl:Fleche.Io.Level.t -> message:string -> unit) ref

(** Start the shell, must be called only once. *)
val init_agent :
  token:Coq.Limits.Token.t -> debug:bool -> roots:string list -> unit Agent.R.t

(** [set_workspace ~root] Sets project and workspace settings from [root].
    [root] needs to be in URI format. If called repeteadly, overrides the
    previous call. *)
val set_workspace :
     token:Coq.Limits.Token.t
  -> debug:bool
  -> root:Lang.LUri.File.t
  -> unit Agent.R.t

val build_doc :
     token:Coq.Limits.Token.t
  -> uri:Lang.LUri.File.t
  -> (Fleche.Doc.t, Agent.Error.t) Result.t

val get_toc :
     token:Coq.Limits.Token.t
  -> doc:Fleche.Doc.t
  -> ( (string * Lang.Ast.Info.t list option) list
     , Petanque.Agent.Error.t )
     Result.t
