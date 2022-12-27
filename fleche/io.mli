module CallBack : sig
  type t =
    { log_error : string -> string -> unit
    ; send_diagnostics :
        uri:string -> version:int -> Types.Diagnostic.t list -> unit
    ; send_fileProgress :
        uri:string -> version:int -> (Types.Range.t * int) list -> unit
    }

  val set : t -> unit
end

module Log : sig
  val error : string -> string -> unit
end

module Report : sig
  val diagnostics : uri:string -> version:int -> Types.Diagnostic.t list -> unit

  val fileProgress :
    uri:string -> version:int -> (Types.Range.t * int) list -> unit
end
