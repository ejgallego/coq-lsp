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
    { trace : string -> ?extra:string -> string -> unit
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
    { trace = (fun _ ?extra:_ _ -> ())
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

module Log = struct
  let trace_ d ?extra m = !CallBack.cb.trace d ?extra m
  let trace d ?extra = Format.kasprintf (fun m -> trace_ d ?extra m)

  let trace_object hdr obj =
    (* Fixme, use the extra parameter *)
    trace hdr "[%s]: @[%a@]" hdr Yojson.Safe.(pretty_print ~std:false) obj

  let feedback feedback =
    if not (CList.is_empty feedback) then
      (* Put feedbacks content here? *)
      let extra = None in
      !CallBack.cb.trace "feedback" ?extra
        "feedback received in non-user facing place"
end

module Report = struct
  let message ~io ~lvl ~message = io.CallBack.message ~lvl ~message
  let msg ~io ~lvl = Format.kasprintf (fun m -> message ~io ~lvl ~message:m)
  let diagnostics ~io ~uri ~version d = io.CallBack.diagnostics ~uri ~version d

  let fileProgress ~io ~uri ~version d =
    io.CallBack.fileProgress ~uri ~version d

  let perfData ~io ~uri ~version pd = io.CallBack.perfData ~uri ~version pd
  let serverVersion ~io vi = io.CallBack.serverVersion vi
  let serverStatus ~io st = io.CallBack.serverStatus st
end
