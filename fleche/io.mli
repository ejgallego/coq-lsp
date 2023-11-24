module Level : sig
  type t

  val error : t
  val warning : t
  val info : t
  val log : t
  val debug : t

  (** Convert to LSP numeric code *)
  val to_int : t -> int
end

module CallBack : sig
  type t =
    { trace : string -> ?extra:string -> string -> unit
          (** Send a log message, [extra] may contain information to be shown in
              verbose mode *)
    ; message : lvl:Level.t -> message:string -> unit
          (** Send a user-visible message *)
    ; diagnostics :
        uri:Lang.LUri.File.t -> version:int -> Lang.Diagnostic.t list -> unit
    ; fileProgress :
        uri:Lang.LUri.File.t -> version:int -> Progress.Info.t list -> unit
    }

  val set : t -> unit
end

module Log : sig
  (** Debug trace *)
  val trace : string -> ?extra:string -> string -> unit

  (** For unexpected feedback, remove eventually or just assert false? *)
  val feedback : Loc.t Coq.Message.t list -> unit
end

module Report : sig
  (** User-visible message *)
  val message : io:CallBack.t -> lvl:Level.t -> message:string -> unit

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
