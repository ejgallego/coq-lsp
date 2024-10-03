(** Messages from Coq *)
module Payload = struct
  type 'l t =
    { range : 'l option
    ; msg : Pp.t
    }

  let make ?range msg = { range; msg }
  let map ~f { range; msg } = { range = Option.map f range; msg }
end

type 'l t = Lang.Diagnostic.Severity.t * 'l Payload.t

let map ~f (lvl, pl) = (lvl, Payload.map ~f pl)
