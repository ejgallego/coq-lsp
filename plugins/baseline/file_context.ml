module Result = struct
  type ('a, 'b) t = ('a, 'b) Stdlib.Result.t =
    | Ok of 'a
    | Error of 'b
end

module Either = struct
  type ('a, 'b) t = ('a, 'b) Stdlib.Either.t =
    | Left of 'a
    | Right of 'b
end

module Point = struct
  type t = Lang.Point.t =
    { line : int
    ; character : int
    ; offset : int
    }

  let empty = { line = 0; character = 0; offset = 0 }
end

module Range = struct
  type t = Lang.Range.t =
    { start : Point.t
    ; end_ : Point.t
    }

  let empty = { start = Point.empty; end_ = Point.empty }

  let to_string { start; end_ } =
    Stdlib.Format.asprintf "%d:%d-%d:%d" start.line start.character end_.line
      end_.character
end

type 'a t =
  { name : string
  ; full_name : string
  ; uri : string
  ; range : Range.t
  ; file_link : string
  ; raw : string
  ; v : 'a
  }

let map ~f fc = { fc with v = f fc.v }

let dummy name raw v =
  { name
  ; full_name = name
  ; uri = "no_uri"
  ; range = Range.empty
  ; file_link = "no_link"
  ; raw
  ; v
  }
