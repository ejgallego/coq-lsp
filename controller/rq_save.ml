(** Several todos here in terms of usability *)

let code = -32803

let print_err ~uri e =
  match e with
  | Coq.Protect.Error.Anomaly (_loc, msg) | User (_loc, msg) ->
    Format.asprintf "Error when saving %s: %a"
      (Lang.LUri.File.to_string_file uri)
      Pp.pp_with msg

let request ~token ~doc =
  match Fleche.Doc.save ~token ~doc with
  | { Coq.Protect.E.r = Interrupted; _ } ->
    Error (code, "save operation interrupted")
  | { Coq.Protect.E.r = Completed (Error e); _ } ->
    let error_msg = print_err ~uri:doc.uri e in
    Error (code, error_msg)
  | { Coq.Protect.E.r = Completed (Ok ()); _ } -> Ok `Null
