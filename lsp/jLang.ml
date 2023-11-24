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

module LUri = struct
  module File = struct
    type t = Lang.LUri.File.t

    let to_yojson uri = `String (Lang.LUri.File.to_string_uri uri)
    let invalid_uri msg obj = raise (Yojson.Safe.Util.Type_error (msg, obj))

    let of_yojson uri =
      match uri with
      | `String uri as obj -> (
        let uri = Lang.LUri.of_string uri in
        match Lang.LUri.File.of_uri uri with
        | Result.Ok t -> Result.Ok t
        | Result.Error msg -> invalid_uri ("failed to parse uri: " ^ msg) obj)
      | obj -> invalid_uri "expected uri string, got json object" obj
  end
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
  type t = Lang.Diagnostic.t

  type _t =
    { range : Range.t
    ; severity : int
    ; message : string
    }
  [@@deriving yojson]

  let to_yojson { Lang.Diagnostic.range; severity; message; extra = _ } =
    let range = Range.conv range in
    let severity = Lang.Diagnostic.Severity.to_int severity in
    let message = Pp.to_string message in
    _t_to_yojson { range; severity; message }
end

let mk_diagnostics ~uri ~version ld : Yojson.Safe.t =
  let diags = List.map Diagnostic.to_yojson ld in
  let uri = Lang.LUri.File.to_string_uri uri in
  let params =
    `Assoc
      [ ("uri", `String uri)
      ; ("version", `Int version)
      ; ("diagnostics", `List diags)
      ]
  in
  Base.mk_notification ~method_:"textDocument/publishDiagnostics" ~params
