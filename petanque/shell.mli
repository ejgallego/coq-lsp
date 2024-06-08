(** I/O handling, by default, print to stderr *)

(** [trace header extra message] *)
val trace_ref : (string -> ?extra:string -> string -> unit) ref

(** [message level message] *)
val message_ref : (lvl:Fleche.Io.Level.t -> message:string -> unit) ref

(** Start the shell, must be called only once. *)
val init_agent : debug:bool -> unit

(** [set_workspace ~root] Sets project and workspace settings from [root].
    [root] needs to be in URI format. If called repeteadly, overrides the
    previous call. *)
val set_workspace :
     token:Coq.Limits.Token.t
  -> debug:bool
  -> root:Lang.LUri.File.t
  -> Agent.Env.t Agent.R.t

(** [setup_doc ~token env uri] Reads a file from [uri] and fully checks it with
    Flèche, returning the doc if succesfull. It will open the file using the env
    passed to set_workspace last time it was called. *)
val setup_doc :
     token:Coq.Limits.Token.t
  -> Agent.Env.t
  -> Lang.LUri.File.t
  -> Fleche.Doc.t Agent.R.t

val fn :
     token:Coq.Limits.Token.t
  -> Lang.LUri.File.t
  -> (Fleche.Doc.t, Agent.Error.t) result
