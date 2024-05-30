module Level = struct
  type t = int

  (* We follow LSP spec *)
  let error = 1
  let warning = 2
  let info = 3
  let log = 4
  let debug = 5
  let to_int x = x
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
  let trace d ?extra m = !CallBack.cb.trace d ?extra m

  let feedback feedback =
    if not (CList.is_empty feedback) then
      (* Put feedbacks content here? *)
      let extra = None in
      !CallBack.cb.trace "feedback" ?extra
        "feedback received in non-user facing place"
end

module Report = struct
  let message ~io ~lvl ~message = io.CallBack.message ~lvl ~message
  let diagnostics ~io ~uri ~version d = io.CallBack.diagnostics ~uri ~version d

  let fileProgress ~io ~uri ~version d =
    io.CallBack.fileProgress ~uri ~version d

  let perfData ~io ~uri ~version pd = io.CallBack.perfData ~uri ~version pd
  let serverVersion ~io vi = io.CallBack.serverVersion vi
  let serverStatus ~io st = io.CallBack.serverStatus st
end
