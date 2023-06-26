module CallBack : sig
  type t =
    { trace : string -> ?extra:string -> string -> unit
          (** Send a log message, [extra] may contain information to be shown in
              verbose mode *)
    ; send_diagnostics :
        uri:Lang.LUri.File.t -> version:int -> Lang.Diagnostic.t list -> unit
    ; send_fileProgress :
        uri:Lang.LUri.File.t -> version:int -> Progress.Info.t list -> unit
    }

  val set : t -> unit
end

module Log : sig
  val trace : string -> ?extra:string -> string -> unit

  (** For unexpected feedback *)
  val feedback : Loc.t Coq.Message.t list -> unit
end

module Report : sig
  val diagnostics :
       io:CallBack.t
    -> uri:Lang.LUri.File.t
    -> version:int
    -> Lang.Diagnostic.t list
    -> unit

  val fileProgress :
       io:CallBack.t
    -> uri:Lang.LUri.File.t
    -> version:int
    -> Progress.Info.t list
    -> unit

  val perfData :
    io:CallBack.t -> uri:Lang.LUri.File.t -> version:int -> Perf.t -> unit
end
