let pp_diag fmt (d : Lang.Diagnostic.t) =
  Format.fprintf fmt "@[%a@]"
    (Yojson.Safe.pretty_print ~std:true)
    (Lsp.JLang.Diagnostic.to_yojson d)

let pp_diags fmt dl =
  Format.fprintf fmt "@[%a@]" (Format.pp_print_list pp_diag) dl

(* We will use this when we set eager diagnotics to true *)
let diagnostics ~uri:_ ~version:_ _diags = ()
let fileProgress ~uri:_ ~version:_ _progress = ()
let perfData ~uri:_ ~version:_ _perf = ()

(* We print trace and messages, and perfData summary *)
module Fcc_verbose = struct
  let trace hdr ?extra message =
    Format.(
      eprintf "[trace] {%s} %s %a@\n%!" hdr message
        (pp_print_option pp_print_string)
        extra)

  let message ~lvl:_ ~message = Format.(eprintf "[message] %s@\n%!" message)

  let perfData ~uri:_ ~version:_ { Fleche.Perf.summary; _ } =
    Format.(eprintf "[perfdata]@\n@[%s@]@\n%!" summary)

  let cb =
    Fleche.Io.CallBack.{ trace; message; diagnostics; fileProgress; perfData }
end

(* We print trace, messages *)
module Fcc_normal = struct
  let trace _ ?extra:_ _ = ()
  let message = Fcc_verbose.message
  let perfData = Fcc_verbose.perfData

  let cb =
    Fleche.Io.CallBack.{ trace; message; diagnostics; fileProgress; perfData }
end

module Fcc_quiet = struct
  let trace _ ?extra:_ _ = ()
  let message ~lvl:_ ~message:_ = ()

  let cb =
    Fleche.Io.CallBack.{ trace; message; diagnostics; fileProgress; perfData }
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

let set_config ~perfData =
  Fleche.Config.(
    v :=
      { !v with
        send_perf_data = perfData
      ; eager_diagnostics = false
      ; show_coq_info_messages = true
      ; show_notices_as_diagnostics = true
      })

let init display ~perfData =
  set_config ~perfData;
  set_callbacks display
