(************************************************************************)
(* Rocq Language Server Protocol                                        *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 EJGA       -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Level = struct
  type t =
    | Error
    | Warning
    | Info
    | Log
    | Debug
end

module CallBack = struct
  type t =
    { trace : string -> ?verbose:string -> string -> unit
    ; message : lvl:Level.t -> message:string -> unit
    ; diagnostics :
        uri:Lang.LUri.File.t -> version:int -> Lang.Diagnostic.t list -> unit
    ; fileProgress :
        uri:Lang.LUri.File.t -> version:int -> Progress.Info.t list -> unit
    ; perfData : uri:Lang.LUri.File.t -> version:int -> Perf.t -> unit
    ; serverVersion : ServerInfo.Version.t -> unit
    ; serverStatus : ServerInfo.Status.t -> unit
    }

  let default =
    { trace = (fun _ ?verbose:_ _ -> ())
    ; message = (fun ~lvl:_ ~message:_ -> ())
    ; diagnostics = (fun ~uri:_ ~version:_ _ -> ())
    ; fileProgress = (fun ~uri:_ ~version:_ _ -> ())
    ; perfData = (fun ~uri:_ ~version:_ _ -> ())
    ; serverVersion = (fun _ -> ())
    ; serverStatus = (fun _ -> ())
    }

  let cb = ref default
  let set t = cb := t
end

(** Trace *)
module TraceValue = struct
  type t =
    | Off
    | Messages
    | Verbose

  let of_string = function
    | "messages" -> Ok Messages
    | "verbose" -> Ok Verbose
    | "off" -> Ok Off
    | v -> Error ("TraceValue.parse: " ^ v)

  let to_string = function
    | Off -> "off"
    | Messages -> "messages"
    | Verbose -> "verbose"
end

module Log = struct
  let trace_value = ref TraceValue.Off
  let set_trace_value value = trace_value := value

  let trace_ d ?verbose m =
    match !trace_value with
    | Off -> ()
    | Messages -> !CallBack.cb.trace d ?verbose:None m
    | Verbose -> !CallBack.cb.trace d ?verbose m

  let trace d ?verbose = Format.kasprintf (fun m -> trace_ d ?verbose m)

  let trace_object hdr obj =
    (* Fixme, use the extra parameter *)
    trace hdr "[%s]: @[%a@]" hdr Yojson.Safe.(pretty_print ~std:false) obj

  let feedback feedback =
    if not (CList.is_empty feedback) then
      (* Put feedbacks content here? *)
      let verbose = None in
      !CallBack.cb.trace "feedback" ?verbose
        "feedback received in non-user facing place"
end

module Report = struct
  let message_ ~io ~lvl ~message = io.CallBack.message ~lvl ~message
  let msg ~io ~lvl = Format.kasprintf (fun m -> message_ ~io ~lvl ~message:m)
  let diagnostics ~io ~uri ~version d = io.CallBack.diagnostics ~uri ~version d

  let fileProgress ~io ~uri ~version d =
    io.CallBack.fileProgress ~uri ~version d

  let perfData ~io ~uri ~version pd = io.CallBack.perfData ~uri ~version pd
  let serverVersion ~io vi = io.CallBack.serverVersion vi
  let serverStatus ~io st = io.CallBack.serverStatus st
end
