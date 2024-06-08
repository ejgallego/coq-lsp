(** I/O handling, by default, print to stderr *)

(** [trace header extra message] *)
val trace_ref : (string -> ?extra:string -> string -> unit) ref

(** [message level message] *)
val message_ref : (lvl:Fleche.Io.Level.t -> message:string -> unit) ref

(** Start the shell, must be called only once. *)
val init_agent :
  token:Coq.Limits.Token.t -> debug:bool -> roots:Lang.LUri.File.t list -> unit

(** [set_workspace ~root] Sets project and workspace settings from [root].
    [root] needs to be in URI format. If called repeteadly, overrides the
    previous call. *)
val set_workspace :
     token:Coq.Limits.Token.t
  -> debug:bool
  -> root:Lang.LUri.File.t
  -> unit Agent.R.t
