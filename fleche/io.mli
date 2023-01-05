module CallBack : sig
  type t =
    { trace : string -> ?extra:string -> string -> unit
          (** Send a log message, [extra] may contain information to be shown in
              verbose mode *)
    ; send_diagnostics :
        uri:string -> version:int -> Types.Diagnostic.t list -> unit
    ; send_fileProgress :
        uri:string -> version:int -> (Types.Range.t * int) list -> unit
    }

  val set : t -> unit
end

module Log : sig
  val trace : string -> ?extra:string -> string -> unit
end

module Report : sig
  val diagnostics : uri:string -> version:int -> Types.Diagnostic.t list -> unit

  val fileProgress :
    uri:string -> version:int -> (Types.Range.t * int) list -> unit
end
