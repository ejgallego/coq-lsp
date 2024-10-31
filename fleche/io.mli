module Level : sig
  type t =
    | Error
    | Warning
    | Info
    | Log
    | Debug
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
    ; perfData : uri:Lang.LUri.File.t -> version:int -> Perf.t -> unit
    ; serverVersion : ServerInfo.Version.t -> unit
    ; serverStatus : ServerInfo.Status.t -> unit
    }

  val set : t -> unit
end

module Log : sig
  (** Debug trace *)
  val trace :
    string -> ?extra:string -> ('a, Format.formatter, unit) format -> 'a

  (** Raw LSP method *)
  val trace_ : string -> ?extra:string -> string -> unit

  (** Log JSON object to server info log *)
  val trace_object : string -> Yojson.Safe.t -> unit

  (** For unexpected feedback, remove eventually or just assert false? *)
  val feedback : Pure.Loc.t Pure.Message.t list -> unit
end

module Report : sig
  (** User-visible message *)
  val msg :
    io:CallBack.t -> lvl:Level.t -> ('a, Format.formatter, unit) format -> 'a

  (** Raw LSP method *)
  val message_ : io:CallBack.t -> lvl:Level.t -> message:string -> unit

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

  val serverVersion : io:CallBack.t -> ServerInfo.Version.t -> unit
  val serverStatus : io:CallBack.t -> ServerInfo.Status.t -> unit
end
