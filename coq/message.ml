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

module LocMessage = struct
  type nonrec t = Loc.t t

  (* Very limited recovering but is not needed. *)
  let of_yojson json : (t, string) result = match json with
    | `Assoc [("state", `String s); ("message", `String m)] ->
      begin match Lang.Diagnostic.Severity.of_string s with
      | Ok s -> Ok (s, { range = None; quickFix = None; msg = Pp.str m})
      | Error e -> Error e
      end
    | _ -> Error "Unable to recover a message with this json object."

  (* let loc_to_yojson loc : Yojson.Safe.t =
    `String (Pp.string_of_ppcmds (Loc.pr loc))

  let quickFix_to_yojson Lang.Qf.{ range ; newText } : Yojson.Safe.t =
    `Assoc [("range", loc_to_yojson range); ("newText", `String newText)] *)

  let to_yojson ((severity, payload) : t) : Yojson.Safe.t =
    `Assoc [
      ("severity", `String (Lang.Diagnostic.Severity.to_string severity));
      (* ("message", `Assoc [
        ("range", match payload.range with
                    | Some l -> loc_to_yojson l
                    | None   -> `String "Not specified");
        ("quickFix", match payload.quickFix with
                      | Some qfl -> `List (List.map quickFix_to_yojson qfl)
                      | None     -> `String "Not specified"); *)
        ("message", `String (Pp.string_of_ppcmds payload.msg))
      (* ]) *)
    ]
end
