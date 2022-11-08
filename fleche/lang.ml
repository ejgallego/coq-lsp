(* XXX: ejgallego, do we start lines at 0? *)
module Point = struct
  type t =
    { line : int
    ; character : int
    ; offset : int
    }
end

module Range = struct
  type t =
    { start : Point.t
    ; _end : Point.t
    }
end

module Loc = struct
  include Loc

  type offset = int * int * int * int * int * int

  let initial ~uri = Loc.initial (InFile { dirpath = None; file = uri })

  let offset (l1 : Loc.t) (l2 : Loc.t) =
    let line_offset = l2.line_nb - l1.line_nb in
    let bol_offset = l2.bol_pos - l1.bol_pos in
    let line_last_offset = l2.line_nb_last - l1.line_nb_last in
    let bol_last_offset = l2.bol_pos_last - l1.bol_pos_last in
    let bp_offset = l2.bp - l1.bp in
    let ep_offset = l2.ep - l1.ep in
    ( line_offset
    , bol_offset
    , line_last_offset
    , bol_last_offset
    , bp_offset
    , ep_offset )

  let apply_offset
      ( line_offset
      , bol_offset
      , line_last_offset
      , bol_last_offset
      , bp_offset
      , ep_offset ) (loc : Loc.t) =
    { loc with
      line_nb = loc.line_nb + line_offset
    ; bol_pos = loc.bol_pos + bol_offset
    ; line_nb_last = loc.line_nb_last + line_last_offset
    ; bol_pos_last = loc.bol_pos_last + bol_last_offset
    ; bp = loc.bp + bp_offset
    ; ep = loc.ep + ep_offset
    }

  let to_range (p : Loc.t) : Range.t =
    let Loc.{ line_nb; line_nb_last; bol_pos; bol_pos_last; bp; ep; _ } = p in
    let start_line = line_nb - 1 in
    let start_col = bp - bol_pos in
    let end_line = line_nb_last - 1 in
    let end_col = ep - bol_pos_last in
    Range.
      { start = { line = start_line; character = start_col; offset = bp }
      ; _end = { line = end_line; character = end_col; offset = ep }
      }
end

module Pp = struct
  include Pp

  let to_string = string_of_ppcmds
end

module Message = Coq.Message
module Init = Coq.Init
module Ast = Coq.Ast
module Parse = Coq.Parse
module State = Coq.State
module Protect = Coq.Protect
module Interp = Coq.Interp
