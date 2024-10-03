(** Messages from Coq *)
module Payload = struct
  type 'l t =
    { range : 'l option
    ; quickFix : 'l Lang.Qf.t list option
    ; msg : Pp.t
    }

  let make ?range ?quickFix msg = { range; quickFix; msg }

  let map ~f { range; quickFix; msg } =
    let quickFix = Option.map (List.map (Lang.Qf.map ~f)) quickFix in
    { range = Option.map f range; quickFix; msg }
end

type 'l t = Lang.Diagnostic.Severity.t * 'l Payload.t

let map ~f (lvl, pl) = (lvl, Payload.map ~f pl)
