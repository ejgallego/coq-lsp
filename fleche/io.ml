module CallBack = struct
  type t =
    { trace : string -> ?extra:string -> string -> unit
    ; send_diagnostics :
           ofn:(Yojson.Safe.t -> unit)
        -> uri:Lang.LUri.File.t
        -> version:int
        -> Lang.Diagnostic.t list
        -> unit
    ; send_fileProgress :
           ofn:(Yojson.Safe.t -> unit)
        -> uri:Lang.LUri.File.t
        -> version:int
        -> Progress.Info.t list
        -> unit
    }

  let default =
    { trace = (fun _ ?extra:_ _ -> ())
    ; send_diagnostics = (fun ~ofn:_ ~uri:_ ~version:_ _ -> ())
    ; send_fileProgress = (fun ~ofn:_ ~uri:_ ~version:_ _ -> ())
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
  let diagnostics ~ofn ~uri ~version d =
    !CallBack.cb.send_diagnostics ~ofn ~uri ~version d

  let fileProgress ~ofn ~uri ~version d =
    !CallBack.cb.send_fileProgress ~ofn ~uri ~version d
end
