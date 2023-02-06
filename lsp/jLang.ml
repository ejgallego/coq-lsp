(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Pp = JCoq.Pp

module Point = struct
  type t = [%import: Lang.Point.t] [@@deriving yojson]
end

module Range = struct
  type t = [%import: (Lang.Range.t[@with Lang.Point.t := Point.t])]
  [@@deriving yojson]
end

module Diagnostic = struct
  module Libnames = Serlib.Ser_libnames

  (* LSP Ranges, a bit different from Fleche's ranges as points don't include
     offsets *)
  module Point = struct
    type t =
      { line : int
      ; character : int
      }
    [@@deriving yojson]

    let conv { Lang.Point.line; character; offset = _ } = { line; character }
  end

  module Range = struct
    type t =
      { start : Point.t
      ; end_ : Point.t [@key "end"]
      }
    [@@deriving yojson]

    let conv { Lang.Range.start; end_ } =
      let start = Point.conv start in
      let end_ = Point.conv end_ in
      { start; end_ }
  end

  (* Current Flèche diagnostic is not LSP-standard compliant, this one is *)
  type t =
    { range : Range.t
    ; severity : int
    ; message : string
    }
  [@@deriving yojson]

  let to_yojson { Lang.Diagnostic.range; severity; message; extra = _ } =
    let message = Pp.to_string message in
    let range = Range.conv range in
    to_yojson { range; severity; message }
end

let mk_diagnostics ~uri ~version ld : Yojson.Safe.t =
  let diags = List.map Diagnostic.to_yojson ld in
  let params =
    `Assoc
      [ ("uri", `String uri)
      ; ("version", `Int version)
      ; ("diagnostics", `List diags)
      ]
  in
  Base.mk_notification ~method_:"textDocument/publishDiagnostics" ~params
