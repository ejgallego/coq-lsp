module CallBack = struct
  type t =
    { trace : string -> ?extra:string -> string -> unit
    ; send_diagnostics :
           ofmt:Format.formatter
        -> uri:string
        -> version:int
        -> Types.Diagnostic.t list
        -> unit
    ; send_fileProgress :
           ofmt:Format.formatter
        -> uri:string
        -> version:int
        -> Progress.Info.t list
        -> unit
    }

  let default =
    { trace = (fun _ ?extra:_ _ -> ())
    ; send_diagnostics = (fun ~ofmt:_ ~uri:_ ~version:_ _ -> ())
    ; send_fileProgress = (fun ~ofmt:_ ~uri:_ ~version:_ _ -> ())
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
  let diagnostics ~ofmt ~uri ~version d =
    !CallBack.cb.send_diagnostics ~ofmt ~uri ~version d

  let fileProgress ~ofmt ~uri ~version d =
    !CallBack.cb.send_fileProgress ~ofmt ~uri ~version d
end
