(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Pp = JCoq.Pp

module Point = struct
  type t = [%import: Lang.Point.t] [@@deriving yojson]

  module Mode = struct
    type t =
      | LineColumn
          (** Points are standard LSP objects with [line] [character] field;
              this is the default *)
      | Offset  (** Points are objects with only the [offset] *)
      | Full
          (** Points include / require [line], [character], and [offset] field *)

    (** Set the mode for serialization. *)
    let default = ref LineColumn

    let set v = default := v
  end

  module PointLC = struct
    type t =
      { line : int
      ; character : int
      }
    [@@deriving yojson]

    let conv { Lang.Point.line; character; offset = _ } = { line; character }
    let vnoc { line; character } = { Lang.Point.line; character; offset = -1 }
  end

  module PointOffset = struct
    type t = { offset : int } [@@deriving yojson]

    let conv { Lang.Point.line = _; character = _; offset } = { offset }
    let vnoc { offset } = { Lang.Point.line = -1; character = -1; offset }
  end

  let of_yojson json =
    let open Ppx_deriving_yojson_runtime in
    match !Mode.default with
    | LineColumn -> PointLC.(of_yojson json >|= vnoc)
    | Offset -> PointOffset.(of_yojson json >|= vnoc)
    | Full -> of_yojson json

  let to_yojson p =
    match !Mode.default with
    | LineColumn -> PointLC.(to_yojson (conv p))
    | Offset -> PointOffset.(to_yojson (conv p))
    | Full -> to_yojson p
end

module Range = struct
  type t = [%import: (Lang.Range.t[@with Lang.Point.t := Point.t])]
  [@@deriving yojson]
end

module LUri = struct
  module File = struct
    type t = Lang.LUri.File.t

    let to_yojson uri = `String (Lang.LUri.File.to_string_uri uri)

    let invalid_uri msg obj =
      let msg =
        Format.asprintf "@[%s@] for object: @[%a@]" msg Yojson.Safe.pp obj
      in
      Error msg

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

module Qf = struct
  type 'l t = [%import: 'l Lang.Qf.t] [@@deriving yojson]
end

module Diagnostic = struct
  module Mode = struct
    type t =
      | String
      | Pp

    let default = ref String
    let set v = default := v
  end

  module Libnames = Serlib.Ser_libnames

  module FailedRequire = struct
    type t = [%import: Lang.Diagnostic.FailedRequire.t] [@@deriving yojson]
  end

  module Data = struct
    type t =
      [%import:
        (Lang.Diagnostic.Data.t
        [@with
          Lang.Qf.t := Qf.t;
          Lang.Range.t := Range.t])]
    [@@deriving yojson]
  end

  module Severity = struct
    type t = [%import: Lang.Diagnostic.Severity.t] [@@deriving yojson]
  end

  module DiagnosticString = struct
    type t =
      { range : Range.t
      ; severity : Severity.t
      ; message : string
      ; data : Data.t option [@default None]
      }
    [@@deriving yojson]

    let conv { Lang.Diagnostic.range; severity; message; data } =
      let message = Pp.string_of_ppcmds message in
      { range; severity; message; data }

    let vnoc { range; severity; message; data } =
      let message = Pp.str message in
      { Lang.Diagnostic.range; severity; message; data }
  end

  type t = [%import: (Lang.Diagnostic.t[@with Lang.Range.t := Range.t])]
  [@@deriving yojson]

  let of_yojson json =
    let open Ppx_deriving_yojson_runtime in
    match !Mode.default with
    | String -> DiagnosticString.(of_yojson json >|= vnoc)
    | Pp -> of_yojson json

  let to_yojson p =
    match !Mode.default with
    | String -> DiagnosticString.(to_yojson (conv p))
    | Pp -> to_yojson p
end

module Stdlib = JStdlib

module With_range = struct
  type 'a t = [%import: ('a Lang.With_range.t[@with Lang.Range.t := Range.t])]
  [@@deriving yojson]
end

module Ast = struct
  module Name = struct
    type t = [%import: Lang.Ast.Name.t] [@@deriving yojson]
  end

  module Info = struct
    type t =
      [%import:
        (Lang.Ast.Info.t
        [@with
          Lang.Range.t := Range.t;
          Lang.With_range.t := With_range.t])]
    [@@deriving yojson]
  end
end
