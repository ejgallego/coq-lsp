module Lsp = Fleche_lsp

let pp_diag fmt (d : Lang.Diagnostic.t) =
  Format.fprintf fmt "@[%a@]"
    (Yojson.Safe.pretty_print ~std:true)
    (Lsp.JLang.Diagnostic.to_yojson d)

let pp_diags fmt dl =
  Format.fprintf fmt "@[%a@]" (Format.pp_print_list pp_diag) dl

(* We will use this when we set eager diagnotics to true *)
let diagnostics ~uri:_ ~version:_ _diags = ()
let fileProgress ~uri:_ ~version:_ _progress = ()

(* We print trace and messages, and perfData summary *)
module Fcc_verbose = struct
  let trace hdr ?verbose message =
    Format.(
      eprintf "[trace] {%s} %s %a@\n%!" hdr message
        (pp_print_option pp_print_string)
        verbose)

  let message ~lvl:_ ~message = Format.(eprintf "[message] %s@\n%!" message)

  let perfData ~uri:_ ~version:_ { Fleche.Perf.summary; _ } =
    Format.(eprintf "[perfdata]@\n@[%s@]@\n%!" summary)

  let serverVersion _ = ()
  let serverStatus _ = ()
  let execInfo ~uri:_ ~version:_ ~range:_ = ()

  let cb =
    Fleche.Io.CallBack.
      { trace
      ; message
      ; diagnostics
      ; fileProgress
      ; perfData
      ; serverVersion
      ; serverStatus
      ; execInfo
      }
end

(* We don't print trace messages, we could also use set_trace_value *)
module Fcc_normal = struct
  let trace _ ?verbose:_ _ = ()
  let cb = { Fcc_verbose.cb with trace }
end

module Fcc_quiet = struct
  let message ~lvl:_ ~message:_ = ()
  let cb = { Fcc_normal.cb with message }
end

let set_callbacks (display : Args.Display.t) =
  let cb =
    match display with
    | Verbose -> Fcc_verbose.cb
    | Normal -> Fcc_normal.cb
    | Quiet -> Fcc_quiet.cb
  in
  Fleche.Io.CallBack.set cb;
  cb

let set_config ~perfData ~coq_diags_level =
  let show_coq_info_messages = coq_diags_level > 1 in
  let show_notices_as_diagnostics = coq_diags_level > 0 in
  Fleche.Config.(
    v :=
      { !v with
        send_perf_data = perfData
      ; eager_diagnostics = false
      ; show_coq_info_messages
      ; show_notices_as_diagnostics
      })

let init ~display ~coq_diags_level ~perfData =
  set_config ~perfData ~coq_diags_level;
  set_callbacks display
