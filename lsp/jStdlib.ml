module Result = struct
  include Stdlib.Result

  type ('a, 'e) t = [%import: ('a, 'e) Stdlib.Result.t] [@@deriving yojson]
end
