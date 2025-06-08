(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)

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
    { trace : string -> ?verbose:string -> string -> unit
          (** Send a log message, [verbose] may contain information to be shown
              in verbose mode *)
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

(** {1 Imperative Tracing using a global [trace_fn]} *)

(** Trace values *)
module TraceValue : sig
  type t =
    | Off
    | Messages
    | Verbose

  val of_string : string -> (t, string) Result.t
  val to_string : t -> string
end

module Log : sig
  (** Set the trace value *)
  val set_trace_value : TraceValue.t -> unit

  (** [trace component ?verbose params] Debug trace, using printf *)
  val trace :
    string -> ?verbose:string -> ('a, Format.formatter, unit) format -> 'a

  (** Direct string-based method *)
  val trace_ : string -> ?verbose:string -> string -> unit

  (** Log JSON object to server info log *)
  val trace_object : string -> Yojson.Safe.t -> unit

  (** For unhandled feedback, for example when running hover, remove eventually? *)
  val feedback : string -> Loc.t Coq.Message.t list -> unit
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
