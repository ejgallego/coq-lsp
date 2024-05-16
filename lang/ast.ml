module Name = struct
  type t = string option
end

(** Information about the Ast, to move to lang *)
module Info = struct
  type t =
    { range : Range.t
    ; parent : string list
    ; name : Name.t With_range.t
    ; kind : int
    ; detail : string option (* usually the type *)
    ; children : t list option
    }

  let make ~range ~parent ~name ~kind ?detail ?children () =
    { range; parent; name; kind; detail; children }
end
