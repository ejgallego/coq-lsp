type token =
  | NULL
  | TRUE
  | FALSE
  | STRING of string
  | INT of int
  | FLOAT of float
  | LEFT_BRACK
  | RIGHT_BRACK
  | LEFT_BRACE
  | RIGHT_BRACE
  | COMMA
  | COLON
  | EOF

module CAst = struct
  type 'a t =
    { v : 'a
    ; range : Lang.Range.t
    }

  let make ~range v = { v; range }
end

type lstring = string CAst.t

type value_r =
  | Assoc of (lstring * value) list
  | Bool of bool
  | Float of float
  | Int of int
  | List of value list
  | Null
  | String of string

and value = value_r CAst.t

let rec find key = function
  | [] -> None
  | ({ CAst.v; _ }, b) :: l -> if compare v key = 0 then Some b else find key l
