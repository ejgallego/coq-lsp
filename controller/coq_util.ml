let coq_protect f x =
  try
    let res = f x in
    Ok res
  with _exn ->
    (* let e, info = Exninfo.capture exn in
     * let loc = Loc.(get_loc info) in
     * let msg = CErrors.iprint (e, info) in
     * Error (loc, msg) *)
    Error (None, Pp.mt ())
